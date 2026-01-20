from loop import Loop
import openai
import re, prompt, string
import requests
import json
import os
import logging
from typing import Tuple, Optional
# from transformers import AutoModelForCausalLM, AutoTokenizer
# from transformers import GenerationConfig

# model_local_path = "/opt/pangu/openPangu-Embedded-1B-V1.1"
# # load the tokenizer and the model
# tokenizer = AutoTokenizer.from_pretrained(
#     model_local_path, 
#     use_fast=False, 
#     trust_remote_code=True,
#     local_files_only=True
# )
# pangumodel = AutoModelForCausalLM.from_pretrained(
#     model_local_path,
#     trust_remote_code=True,
#     torch_dtype="auto",
#     device_map="npu",
#     local_files_only=True
# )

def scan_clause_from(text: str, start_pos: int) -> Tuple[Optional[str], int]:
    i = start_pos
    n = len(text)
    buf = []
    paren = 0   # ( )
    brack = 0   # [ ]
    brace = 0   # { }
    skip_header_semicolon = 0  # 若>0表示最近遇到 \forall 或 \exists，需要跳过接下来的一个分号（头部分号）
    # 为了正确识别量词，需检测反斜杠后面是 forall 或 exists
    while i < n:
        ch = text[i]
        # 检测量词启动：\forall 或 \exists（允许前后空白）
        if ch == '\\':
            # check following word
            m = re.match(r"\\(forall|exists)\b", text[i:])
            if m:
                # copy the matched text into buffer, advance i
                token = m.group(0)
                buf.append(token)
                i += len(token)
                # after a quantifier, the header will contain a semicolon that we must skip once
                # (there may be multiple quantifiers, so increment skip count)
                skip_header_semicolon += 1
                continue
        # track brackets/parens
        if ch == '(':
            paren += 1
            buf.append(ch); i += 1; continue
        if ch == ')':
            if paren > 0: paren -= 1
            buf.append(ch); i += 1; continue
        if ch == '[':
            brack += 1
            buf.append(ch); i += 1; continue
        if ch == ']':
            if brack > 0: brack -= 1
            buf.append(ch); i += 1; continue
        if ch == '{':
            brace += 1
            buf.append(ch); i += 1; continue
        if ch == '}':
            if brace > 0: brace -= 1
            buf.append(ch); i += 1; continue

        # semicolon handling
        if ch == ';':
            # if inside any brackets/parens/braces, this semicolon likely part of an expression -> keep scanning
            if paren > 0 or brack > 0 or brace > 0:
                buf.append(ch); i += 1; continue
            # if we have pending quantifier header semicolons to skip, skip one
            if skip_header_semicolon > 0:
                # consume this semicolon as header separator, decrement counter and continue
                skip_header_semicolon -= 1
                buf.append(ch)  # we may keep it inside buffer (or omit). We keep it since body may rely on it.
                i += 1
                continue
            # Otherwise this semicolon ends the clause
            clause = ''.join(buf).strip()
            return clause, i + 1
        # normal char
        buf.append(ch)
        i += 1

    # reached EOF without semicolon terminator
    clause = ''.join(buf).strip()
    if clause:
        return clause, n
    return None, n

class LoopList:
    def __init__(self, code, filename, model, logger) -> None:
        self.loop_list: list[Loop] = []
        self.filename = filename
        self.invid = 0
        self.model = model
        self.logger: logging.Logger = logger
        self.code = self.inject_loop_index_into_code(code)
        self.error_count = {}
        self.ensures: dict = self.extract_function_ensures(self.code, self.filename)

    def logger_inv(self):
        self.logger.info("------------Invariant Info-----------")
        for lp in self.loop_list:
            inv_lis = lp.loop_invariant
            self.logger.info(f"LOOP {lp.alphabet}:")
            for k, v in inv_lis.items():
                 self.logger.info(f"{k}: {v}")
        self.logger.info("------------------------------------")
            
    def remove_all_invariants(self):
        for lp in self.loop_list:
            lp.loop_invariant.clear()
            
    def extract_function_ensures(self, code: str, func_name: str) -> dict:
        ensures_dict = {}
        auto_index = 1

        # --------------------------------------------------
        # Part 1: 原有逻辑 —— 提取函数前的 ensures
        # --------------------------------------------------
        comment_blocks = []
        for m in re.finditer(r"/\*@(?P<comment>.*?)\*/", code, re.DOTALL):
            comment_blocks.append((m.start(), m.group("comment")))

        func_def_match = re.search(r"\b" + re.escape(func_name) + r"\s*\(", code)
        if not func_def_match:
            return {}

        func_pos = func_def_match.start()

        selected_comment = None
        last_pos = -1
        for pos, comment in comment_blocks:
            if pos < func_pos and pos > last_pos:
                last_pos = pos
                selected_comment = comment

        if selected_comment:
            cb = selected_comment
            for m in re.finditer(r"ensures\b", cb):
                abs_start = m.end()
                clause, _ = scan_clause_from(cb, abs_start)
                if clause is None:
                    continue

                lab_m = re.match(r"\s*([A-Za-z0-9_]+)\s*:\s*(.*)", clause, re.DOTALL)
                if lab_m:
                    label = lab_m.group(1)
                    body = lab_m.group(2).strip()
                else:
                    label = str(auto_index)
                    body = clause.strip()
                    auto_index += 1

                body = re.sub(r"\s+", " ", body)
                ensures_dict[label] = body

        # --------------------------------------------------
        # Part 2: 新增逻辑 —— 提取函数体内 //@ assert
        # --------------------------------------------------

        # 1. 定位函数体起始 '{'
        brace_pos = code.find("{", func_def_match.end())
        if brace_pos == -1:
            return ensures_dict

        # 2. 简单括号匹配定位函数体结束
        depth = 0
        end_pos = -1
        for i in range(brace_pos, len(code)):
            if code[i] == "{":
                depth += 1
            elif code[i] == "}":
                depth -= 1
                if depth == 0:
                    end_pos = i
                    break

        if end_pos == -1:
            return ensures_dict

        func_body = code[brace_pos:end_pos]

        # 3. 扫描 //@ assert
        for m in re.finditer(r"//@\s*assert\b(.*?);", func_body, re.DOTALL):
            clause = m.group(1).strip()

            lab_m = re.match(r"([A-Za-z0-9_]+)\s*:\s*(.*)", clause, re.DOTALL)
            if lab_m:
                label = lab_m.group(1)
                body = lab_m.group(2).strip()
            else:
                label = str(auto_index)
                body = clause
                auto_index += 1

            body = re.sub(r"\s+", " ", body)
            ensures_dict[label] = body

        return ensures_dict


    def update_error_count(self, error_msg):
        if self.error_count.get(error_msg) != None:
            self.error_count[error_msg] += 1
        elif self.error_count.get(error_msg) == None:
            self.error_count[error_msg] = 0
        
    
    def loop_graph_construct(self):
        id2loop = {lp.index: lp for lp in self.loop_list}

        parent = {}
        for lp in self.loop_list:
            if isinstance(lp.loop_state, list):  
                for child_idx in lp.loop_state:
                    parent[child_idx] = lp.index

        layers = {}
        for lp in self.loop_list:
            p = parent.get(lp.index, None)
            layers.setdefault(p, []).append(lp.index)


        for lp in self.loop_list:
            pid = parent.get(lp.index, None)
            same_layer = layers.get(pid, [])
            idx_in_layer = same_layer.index(lp.index)


            if idx_in_layer == 0:
                lp.pre_loop = pid if pid is not None else -1
            else:
                lp.pre_loop = same_layer[idx_in_layer - 1]

            if isinstance(lp.loop_state, list) and lp.loop_state:
      
                inner_first = lp.loop_state[0]
                next_same = same_layer[idx_in_layer + 1] if idx_in_layer < len(same_layer) - 1 else "inf"
                post = [inner_first]
                if next_same is not None:
                    post.append(next_same)
                lp.post_loop = post
            else:
            
                if idx_in_layer < len(same_layer) - 1:
                    lp.post_loop = same_layer[idx_in_layer + 1]
                else:
                    lp.post_loop = pid if pid is not None else float("inf")

    def add_loop(self, loop: Loop):
        self.loop_list.append(loop)
    
    def remove_invariant_by_id(self, invid):
        loopidx = self.search_invariant_by_id(invid)
        if loopidx != None:
            self.loop_list[loopidx].loop_invariant.pop(invid, f'No Loop Invariant \"{invid}\" in C program !')

    def search_invariant_by_id(self, invid):
        for lp in self.loop_list:
            loop_inv_list: dict = lp.loop_invariant
            if loop_inv_list.get(invid) != None:
                return lp.index
        return None

    def search_invariant_content_by_id(self, invid):
        for lp in self.loop_list:
            loop_inv_list: dict = lp.loop_invariant
            if loop_inv_list.get(invid) != None:
                return loop_inv_list.get(invid)
        return None

    def get_llm_answer(self, promptcontent):
        if "openPangu" not in self.model:
            client = openai.OpenAI(
                base_url="https://openrouter.ai/api/v1",
                api_key="",
            )
            completion = client.chat.completions.create(
                extra_body={},
                model=self.model,
                messages=[{"role": "user", "content": promptcontent}]
            )

            self.logger.info("----------Prompt----------")
            self.logger.info(promptcontent)
            self.logger.info("--------------------------")
            llm_content = completion.choices[0].message.content
            self.logger.info("----------Response----------")
            self.logger.info(llm_content)
            self.logger.info("----------------------------")
            return llm_content
        
        elif "openPangu" in self.model:
            messages = [
                {"role": "system", "content": prompt.sys_prompt}, 
                {"role": "user", "content": promptcontent}
            ]
            text = tokenizer.apply_chat_template(
                messages,
                tokenize=False,
                add_generation_prompt=True
            )
            model_inputs = tokenizer([text], return_tensors="pt").to(pangumodel.device)
            # conduct text completion
            outputs = pangumodel.generate(**model_inputs, max_new_tokens=32768, eos_token_id=45892, return_dict_in_generate=True)
            input_length = model_inputs.input_ids.shape[1]
            generated_tokens = outputs.sequences[:, input_length:]
            content = tokenizer.decode(generated_tokens[0], skip_special_tokens=True)
            return content


    def extract_loop_invariants(self, text: str):
        """
        解析 LLM 输出两种格式：
        - 纯条目列表： loop invariant ...;
        - 分块形式： [Loop A] ... [Loop B] ...
        返回:
        - 若无分块 -> list of invariants (strings)
        - 若有分块 -> dict { "A": [inv1, inv2], ... }
        """

        text = text.strip()
        # detect blocks first
        # split into tokens while preserving block headers
        block_matches = list(re.finditer(r"\[Loop\s+([A-Za-z0-9_]+)\]", text))
        if not block_matches:
            # scan all occurrences of "loop invariant"
            res = []
            for m in re.finditer(r"loop\s+invariant", text):
                start = m.end()
                clause, nextpos = scan_clause_from(text, start)
                if clause:
                    # remove possible leading 'i_0:' or similar label
                    clause = re.sub(r"^[A-Za-z0-9_]+\s*:\s*", "", clause).strip()
                    # normalize whitespace
                    clause = re.sub(r"\s+", " ", clause)
                    res.append(clause)
            return res

        # has blocks: iterate through blocks and text regions between them
        result = {}
        # We'll walk through block_matches and extract region after each header up to next header or EOF
        n = len(text)
        for idx, m in enumerate(block_matches):
            block_name = m.group(1)
            start_region = m.end()
            end_region = block_matches[idx + 1].start() if idx + 1 < len(block_matches) else n
            region_text = text[start_region:end_region]
            # in region_text find all loop invariant clauses
            invariants = []
            # search for 'loop invariant' occurrences inside region_text, but need absolute index
            base = start_region
            for mm in re.finditer(r"loop\s+invariant", region_text):
                abs_start = base + mm.end()
                clause, _ = scan_clause_from(text, abs_start)
                if clause:
                    clause = re.sub(r"^[A-Za-z0-9_]+\s*:\s*", "", clause).strip()
                    clause = re.sub(r"\s+", " ", clause)
                    invariants.append(clause)
            result[block_name] = invariants
        return result


    def get_pre_loop_invariant(self, current_loop: Loop):
        if current_loop.pre_loop != -1:
            pre_loop: Loop = self.loop_list[current_loop.pre_loop]
            result = ""
            for invid, inv in pre_loop.loop_invariant.items():
                result += str(invid) + ':' + str(inv) + '; '
            return result
        else:
            return "the function's `requires` clauses"

    def get_post_loop_invariant(self, current_loop: Loop):
        if isinstance(current_loop.post_loop, list):
            for id in current_loop.post_loop:
                if str(id) != "inf":
                    result = ""
                    post_loop: Loop = self.loop_list[id]
                    for invid, inv in post_loop.loop_invariant.items():
                        result += str(invid) + ':' + str(inv) + '; '
                    return result
                else:
                    result = ""
                    for enid, en in self.ensures.items():
                        result += str(enid) + ':' + str(en) + '; '
                    return result
        else:
            if str(current_loop.post_loop) != "inf":
                result = ""
                post_loop: Loop = self.loop_list[current_loop.post_loop]
                for invid, inv in post_loop.loop_invariant.items():
                    result += str(invid) + ':' + str(inv) + '; '
                return result
            else:
                result = ""
                for enid, en in self.ensures.items():
                    result += str(enid) + ':' + str(en) + '; '
                return result

    
    def get_llm_reasoning_answer(self, prompt_type: str, current_loop: Loop, error_invariant: str = ""):
        """
        一个统一入口，根据 error_type 选择合适模板。
        """
        if prompt_type == "initial_reasoning":
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index,
                hint = "[Hint] Please infer the loop invariant for the following loop."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop, pre_condition = self.get_pre_loop_invariant(current_loop), post_condition=self.get_post_loop_invariant(current_loop))
        elif prompt_type == "initial_reasoning_ablation":
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index,
                hint = "[Hint] Please infer the loop invariant for the following loop."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop)
        elif prompt_type == "ensure":
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index,
                hint = "[Hint] Please strengthen the loop invariant in the following loop."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop, error_invariant)
        elif prompt_type == "establishment_requires":
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index,
                hint = f"[Hint] Loop invariant {error_invariant} too strong initially. Relax it."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop, error_invariant)
        elif prompt_type == "establishment_cross":
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index, 
                hint = f"[Hint] Invariant {error_invariant} not initially provable. Fix or supplement invariants in the pre-loop or in this loop."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop, error_invariant)
        elif prompt_type == "preservation_nested":
            inner_last = current_loop.loop_state[-1]
            inner_loop = self.loop_list[inner_last]
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index,
                hint = f"[Hint] Invariant {error_invariant} not preserved. Fix or supplement invariants the last inner loop or in this loop."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop, error_invariant, inner_loop)
        elif prompt_type == "preservation_self":
            code_with_hint = self.inject_reasoning_prompt_code(
                loop_index = current_loop.index,
                hint = f"[Hint] Invariant {error_invariant} not preserved in this loop. Fix or supplement invariants."
                )
            prompt_content = prompt.get_prompt(code_with_hint, prompt_type, current_loop, error_invariant)
        
        llm_response = self.get_llm_answer(prompt_content)
        dict_or_list = self.extract_loop_invariants(llm_response)
        if isinstance(dict_or_list, dict):
            return dict_or_list
        elif isinstance(dict_or_list, list):
            return {str(current_loop.alphabet) : dict_or_list}

    def initial_loop_invariant_inference(self):
        n = len(self.loop_list)
        for i in range(n):
            if i % 2 == 0:
                current_idx = i // 2
            else:
                current_idx = n - 1 - (i // 2)
            
            current_loop = self.loop_list[current_idx]

            llm_reasoning_answer = self.get_llm_reasoning_answer("initial_reasoning", current_loop)
            self.apply_llm_invariants(llm_reasoning_answer)

    def initial_loop_invariant_inference_ablation(self):
        n = len(self.loop_list)
        for i in range(n):
            if i % 2 == 0:
                current_idx = i // 2
            else:
                current_idx = n - 1 - (i // 2)
            
            current_loop = self.loop_list[current_idx]

            llm_reasoning_answer = self.get_llm_reasoning_answer("initial_reasoning_ablation", current_loop)
            self.apply_llm_invariants(llm_reasoning_answer)

    def apply_llm_invariants(self, llm_answer_dict):
        """
        llm_answer_dict 形如:
        {
            "A": ["inv1", "inv2"],
            "C": ["inv3"]
        }
        """
        letter2id = {chr(ord('A') + i): lp.index for i, lp in enumerate(self.loop_list)}
        for letter, inv_list in llm_answer_dict.items():
            if letter not in letter2id:
                continue
            loop_index = letter2id[letter]
            loop_obj: Loop = self.loop_list[loop_index]
            for inv in inv_list:
                if inv in loop_obj.loop_invariant.values():
                    continue
                loop_obj.loop_invariant[f"i_{self.invid}"] = inv
                self.invid += 1


    def revise_loop_invariant_inference(self, error_msg_key, error_msg_value):
        # ensure 失败
        if error_msg_key.startswith("e") or error_msg_key.startswith("a"):
            target_loop = self.loop_list[-1]
            self.logger.info(f"-------------Ensure Revise: {error_msg_key}: {error_msg_value}---------------")
            llm_reasoning_answer = self.get_llm_reasoning_answer(
                prompt_type = "ensure",
                current_loop = target_loop, 
                error_invariant=error_msg_value
            )
            self.apply_llm_invariants(llm_reasoning_answer)
            return
        
        error_loop_invariant = self.search_invariant_content_by_id(error_msg_key)

        error_loop_index = self.search_invariant_by_id(error_msg_key)
        if error_loop_index is None:
            # print(f"Cannot locate invariant {error_msg_key}")
            return
        current_loop = self.loop_list[error_loop_index]
        # print(f"Revising invariant {error_msg_key} in Loop {error_loop_index}, type={error_msg_value}")

        # invariant 失败
        if error_msg_key.startswith("i"):
            # ① 完全错误 → 直接删除
            if error_msg_value == "both":
                self.remove_invariant_by_id(error_msg_key)
                # logger.info(f"Removed invalid invariant {error_msg_key} (type=both)")
                return
            
            # ② establishment 失败
            if error_msg_value == "establishment":
                pre_idx = current_loop.pre_loop
                if pre_idx == -1:
                    self.logger.info(f"-------------Establishment_requires: {error_msg_key}: {error_msg_value}---------------")
                    llm_reasoning_answer = self.get_llm_reasoning_answer(
                        prompt_type="establishment_requires",
                        current_loop=current_loop,
                        error_invariant=error_loop_invariant
                    )
                else:
                    self.logger.info(f"-------------Establishment_cross: {error_msg_key}: {error_msg_value}---------------")
                    llm_reasoning_answer = self.get_llm_reasoning_answer(
                        prompt_type="establishment_cross",
                        current_loop=current_loop,
                        error_invariant=error_loop_invariant
                    )
                self.apply_llm_invariants(llm_reasoning_answer)
                return

            # ③ preservation 失败
            if error_msg_value == "preservation":
                if isinstance(current_loop.loop_state, list):
                    # 有内部循环
                    self.logger.info(f"-------------Preservation_nested: {error_msg_key}: {error_msg_value}---------------")
                    llm_reasoning_answer = self.get_llm_reasoning_answer(
                        prompt_type="preservation_nested",
                        current_loop=current_loop,
                        error_invariant=error_loop_invariant
                    )
                else:
                    # 无内部循环
                    self.logger.info(f"-------------Preservation_self: {error_msg_key}: {error_msg_value}---------------")
                    llm_reasoning_answer = self.get_llm_reasoning_answer(
                        prompt_type="preservation_self",
                        current_loop=current_loop,
                        error_invariant=error_loop_invariant
                    )
                self.apply_llm_invariants(llm_reasoning_answer)
                return

    def inject_loop_index_into_code(self, code):
        """
        在指定函数体中，每个循环前的 ACSL 注释块前插入 Loop A/B/C/... 提示。
        缩进根据注释块内 loop assigns 的缩进确定。
        """
        # 1. 定位函数体
        func_header_re = re.compile(r'\b' + re.escape(self.filename) + r'\s*\([^)]*\)\s*\{', re.S)
        m_func = func_header_re.search(code)
        if not m_func:
            raise ValueError(f"函数 {self.filename} 未在源码中找到。")

        body_start = m_func.end()
        brace = 0
        body_end = None
        for i, ch in enumerate(code[body_start - 1:], start=body_start - 1):
            if ch == '{':
                brace += 1
            elif ch == '}':
                brace -= 1
                if brace == 0:
                    body_end = i + 1
                    break
        if body_end is None:
            raise ValueError("未能解析函数体结束位置。")

        body = code[body_start:body_end - 1]

        # 2. 匹配每个循环前的 ACSL 注释
        loop_pat = re.compile(
            r'(?P<indent>[ \t]*)/\*@(?P<comment>.*?)\*/\s*(?P<header>(?:for|while)\s*\(.*?\)\s*\{)',
            re.S
        )
        matches = list(loop_pat.finditer(body))

        # 3. 构造新的函数体
        new_body = body
        offset = 0
        alphabet = string.ascii_uppercase  # A, B, C, D...

        for idx, m in enumerate(matches):
            indent = m.group("indent")
            comment_block = m.group("comment")

            # 尝试检测 loop assigns 的缩进（用于决定 Loop 标记缩进）
            assign_indent_match = re.search(r"(\n[ \t]*)loop assigns", comment_block)
            if assign_indent_match:
                extra_indent = assign_indent_match.group(1)
                spaces = len(extra_indent.expandtabs(4)) - 1  # relative to comment block start
                label_indent = " " * max(spaces - 4, 0)
            else:
                # 如果没有 loop assigns，就用注释块的前导缩进
                label_indent = indent

            label_char = alphabet[idx] if idx < len(alphabet) else f"Z{idx - 25}"
            label_line = f"{label_indent}// Loop {label_char}\n"

            insert_pos = m.start() + offset  # 注释块前插入
            new_body = new_body[:insert_pos] + label_line + new_body[insert_pos:]
            offset += len(label_line)

        # 4. 拼回全局代码
        new_code = code[:body_start] + new_body + code[body_end - 1:]
        return new_code

    def inject_reasoning_prompt_code(self, loop_index: int, hint: str = "[Hint] Please infer the loop invariant for the following loop.") -> str:
        code = self.inject_invariants()
        func_header_re = re.compile(r'\b' + re.escape(self.filename) + r'\s*\([^)]*\)\s*\{', re.S)
        m_func = func_header_re.search(code)
        if not m_func:
            raise ValueError(f"函数 {self.filename} 未在源码中找到。")

        body_open_pos = m_func.end()
        brace = 0
        body_end_pos = None
        for i, ch in enumerate(code[body_open_pos - 1:], start=body_open_pos - 1):
            if ch == '{':
                brace += 1
            elif ch == '}':
                brace -= 1
                if brace == 0:
                    body_end_pos = i + 1
                    break
        if body_end_pos is None:
            raise ValueError("未能解析出函数体的闭合 '}'。")

        body = code[body_open_pos:body_end_pos - 1]


        loop_pat = re.compile(
            r'/\*@(?P<comment>.*?)\*/\s*(?P<header>(?:for|while)\s*\(.*?\)\s*\{)',
            re.S,
        )
        matches = list(loop_pat.finditer(body))
        if not matches:
            raise ValueError(f"函数 {self.filename} 中未找到带注释的循环。")

        if loop_index < 0 or loop_index >= len(matches):
            raise IndexError(f"循环索引 {loop_index} 超出范围（共 {len(matches)} 个循环）。")


        m = matches[loop_index]
        cm_match = re.match(r'/\*@.*?\*/', m.group(0), re.S)
        if not cm_match:
            raise ValueError(f"无法识别第 {loop_index} 个循环的注释边界。")

        cm_local_start = m.start() + cm_match.start()
        cm_local_end = m.start() + cm_match.end()
        original_comment_full = body[cm_local_start:cm_local_end]
        inner = original_comment_full[len("/*@"):-len("*/")]


        assign_indent_match = re.search(r'\n([ \t]*)loop assigns', inner)
        if assign_indent_match:
            indent = assign_indent_match.group(1)
        else:
   
            indent = "    "


        prompt_line = f"\n{indent}{hint}\n"


        insert_pos = cm_local_start + len("/*@")
        new_body = body[:insert_pos] + prompt_line + body[insert_pos:]


        new_code = code[:body_open_pos] + new_body + code[body_end_pos - 1:]

        return new_code

    def inject_invariants(self) -> str:
        func_header_re = re.compile(
            r'\b' + re.escape(self.filename) + r'\s*\([^)]*\)\s*\{', re.S
        )
        m_func = func_header_re.search(self.code)
        if not m_func:
            raise ValueError(f"函数 {self.filename} 未在源码中找到。")

        body_open_pos = m_func.end()
        brace = 0
        body_end_pos = None
        for i, ch in enumerate(self.code[body_open_pos-1:], start=body_open_pos-1):
            if ch == '{':
                brace += 1
            elif ch == '}':
                brace -= 1
                if brace == 0:
                    body_end_pos = i + 1
                    break
        if body_end_pos is None:
            raise ValueError("未能解析出函数体的闭合 '}'。")

        body = self.code[body_open_pos:body_end_pos-1]

        loop_pat = re.compile(
            r'/\*@(?P<comment>.*?)\*/\s*(?P<header>(?:for|while)\s*\(.*?\)\s*\{)',
            re.S,
        )
        matches = list(loop_pat.finditer(body))
        if not matches:
            print(f"警告：函数 {self.filename} 中未找到带注释的循环。")

        new_body = body
        offset = 0

        for idx, lp in enumerate(self.loop_list):
            invariants: dict = lp.loop_invariant
            if not invariants:
                continue

            if idx >= len(matches):
                print(f"警告：找不到第 {idx+1} 个循环对应的注释块，跳过注入。")
                continue

            m = matches[idx]
            sub = m.group(0)
            cm_match = re.match(r'/\*@.*?\*/', sub, re.S)
            if not cm_match:
                print(f"警告：无法识别第 {idx+1} 个循环的注释边界，跳过。")
                continue

            cm_local_start = m.start() + cm_match.start()
            cm_local_end = m.start() + cm_match.end()

            original_comment_full = new_body[
                cm_local_start + offset : cm_local_end + offset
            ]
            inner = original_comment_full[len("/*@"):-len("*/")]

            assign_indent = "    "  
            assign_match = re.search(r'(^[ \t]*)loop assigns', inner, re.M)
            if assign_match:
                assign_indent = assign_match.group(1)  
            else:
                first_line_match = re.search(r'(^[ \t]*)', inner)
                if first_line_match:
                    assign_indent = first_line_match.group(1) + "    "

            inv_lines = "".join([
                f"{assign_indent}loop invariant {id}: {inv};\n\n"
                for id, inv in invariants.items()
            ])

            if 'loop assigns' in inner:
                def repl(m_assign):
                    indent = m_assign.group(1)
                    return f"{inv_lines}\n{indent}loop assigns"

                new_inner = re.sub(
                    r'(^[ \t]*)loop assigns',
                    repl,
                    inner,
                    count=1,
                    flags=re.M,
                )
            else:
                new_inner = inner.rstrip() + inv_lines + "\n"

            new_comment_full = "/*@" + new_inner + "*/"

            new_body = (
                new_body[: cm_local_start + offset]
                + new_comment_full
                + new_body[cm_local_end + offset :]
            )
            offset += len(new_comment_full) - (cm_local_end - cm_local_start)

        new_code = (
            self.code[:body_open_pos]
            + new_body
            + self.code[body_end_pos - 1:]
        )

        return new_code

def clean_lines_block(lines):
    filtered = []
    in_comment = False
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        if not in_comment and '/*' in s:
            if '*/' in s:
                continue
            in_comment = True
            continue
        if in_comment:
            if '*/' in s:
                in_comment = False
            continue
        if s in ('{', '}', '};'):
            continue
        filtered.append(s)
    return " ".join(filtered).strip()

def detect_loops_and_positions(body: str):
    loop_pat = re.compile(r'/\*@(?P<comment>.*?)\*/\s*(?P<header>(for|while)\s*\(.*?\)\s*\{)', re.S)
    matches = list(loop_pat.finditer(body))
    lines = body.splitlines()
    loop_infos = []
    for idx, m in enumerate(matches):
        loop_header_pos = body.find('{', m.start())
        start_line = body[:loop_header_pos].count('\n') + 1
        brace_stack = []
        start_pos = loop_header_pos
        for i, ch in enumerate(body[start_pos:], start=start_pos):
            if ch == '{':
                brace_stack.append('{')
            elif ch == '}':
                brace_stack.pop()
                if not brace_stack:
                    end_line = body[:i].count('\n') + 1
                    break
        else:
            end_line = len(lines)
        loop_infos.append({
            'index': idx,
            'comment': m.group('comment'),
            'header': m.group('header'),
            'start': start_line,
            'end': end_line
        })
    return loop_infos, lines

def build_loops(code: str, filename: str, model: str, logger: logging.Logger) -> LoopList:
    func_body_match = re.search(f'{filename}' + r'*\(.*?\)\s*\{(.*)\}', code, re.S)
    body = func_body_match.group(1)
    loop_infos, lines = detect_loops_and_positions(body)
    # nested
    nested = {i: [] for i in range(len(loop_infos))}
    for i in range(len(loop_infos)):
        for j in range(len(loop_infos)):
            if i==j: continue
            if loop_infos[i]['start'] < loop_infos[j]['start'] and loop_infos[i]['end'] > loop_infos[j]['end']:
                nested[i].append(j)

    loops = []
    for i, info in enumerate(loop_infos):
        start_idx = info['start'] - 1
        end_idx = info['end'] - 1
        prev_end_idx = loop_infos[i-1]['end'] if i>0 else 0
        next_start_idx = loop_infos[i+1]['start'] - 1 if i < len(loop_infos)-1 else len(lines)

        # pre_state
        pre_block_lines = lines[prev_end_idx:start_idx]
        pre_state = clean_lines_block(pre_block_lines)

        # for
        header = info['header']
        if header.strip().startswith('for'):
            inside = re.search(r'for\s*\((.*?)\)', header).group(1)
            parts = [p.strip() for p in inside.split(';')]
            if len(parts) >= 1 and parts[0]:
                pre_state = (pre_state + " " + (parts[0] + ";")).strip() if pre_state else (parts[0] + ";")

        # post_state
        post_block_lines = lines[end_idx+1: next_start_idx]
        post_state = clean_lines_block(post_block_lines)

        # loop_body
        body_inner_lines = lines[start_idx+1:end_idx]
        loop_body = clean_lines_block(body_inner_lines)

        # loop assigns
        assigns = re.findall(r'loop assigns (.*?);', info['comment'])

        # condition / update
        cond = ''
        update = ''
        if header.strip().startswith('for'):
            inside = re.search(r'for\s*\((.*?)\)', header).group(1)
            parts = [p.strip() for p in inside.split(';')]
            if len(parts) == 3:
                cond = parts[1]
                update = parts[2]
        else:
            cond = re.search(r'\((.*?)\)', header).group(1)

        # loop_state
        if nested[i]:
            loop_state = [ loop_infos[j]['index'] for j in nested[i] ]
        else:
            loop_state = loop_body
            if update:
                update_stmt = update if update.endswith(';') else update + ';'
                loop_state = (loop_state + " " + update_stmt).strip() if loop_state else update_stmt

        loop_obj = Loop(
            index=info['index'],
            loop_type='for' if header.strip().startswith('for') else 'while',
            pre_state=pre_state,
            condition=cond,
            loop_state=loop_state,
            post_state=post_state,
            loop_assigns=assigns,
            loop_invariant={}
        )
        loops.append(loop_obj)

    loop_list = LoopList(code, filename, model, logger)

    for lp in loops:
        loop_list.add_loop(lp)
    
    loop_list.loop_graph_construct()
    return loop_list

if __name__ == "__main__":
    with open("/home/wgy/algorithm/Benchmark/OOPSLA/oopsla_17.c", "r", encoding="utf-8") as f:
        c = f.read()

    loop_list: LoopList = build_loops(c, 'oopsla_17', 'deepseek/deepseek-chat-v3-0324', None)


    print("=== Output ===\n")
    for lp in loop_list.loop_list:
        print(f"Loop #{lp.index} ({lp.loop_type})")
        print(f"  pre_state: {lp.pre_state}")
        print(f"  condition: {lp.condition}")
        print(f"  loop_state: {lp.loop_state}")
        print(f"  post_state: {lp.post_state}")
        print(f"  loop_assigns: {lp.loop_assigns}") 
        print(f"  loop_invariant: {lp.loop_invariant}")
        print(f"  pre_loop: {lp.pre_loop}")
        print(f"  post_loop: {lp.post_loop}\n")
    
    print(loop_list.ensures)