import re
from typing import Tuple, Optional

# ---------- 辅助扫描器 ----------
def scan_clause_from(text: str, start_pos: int) -> Tuple[Optional[str], int]:
    """
    从 text[start_pos] 开始扫描，返回（clause_text, next_pos）。
    clause_text: 截取到的条目内容（不含结尾分号），若未找到返回 (None, start_pos)
    next_pos: 返回位置是结尾分号后的位置（用于继续搜索）
    扫描策略：跳过量词头部的分号（例如 '\forall ...;')，跳过括号内分号。
    """
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

# ---------- 提取 LLM 输出中的 loop invariant（支持块与多行） ----------
def extract_loop_invariants_text(text: str):
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


# ---------- 从源码注释块中提取 ensures（支持多行并跳过量词头部分号） ----------
def extract_function_ensures_from_code(code: str, func_name: str) -> dict:
    """
    在 code 中找到最接近 func_name 的前面的注释块，并从中提取 ensures，支持跨行量词等情况。
    """
    # find all comment blocks
    comment_blocks = []
    for m in re.finditer(r"/\*@(?P<comment>.*?)\*/", code, re.DOTALL):
        comment_blocks.append((m.start(), m.group("comment")))

    if not comment_blocks:
        return {}

    # find function definition position
    func_def_match = re.search(r"\b" + re.escape(func_name) + r"\s*\(", code)
    if not func_def_match:
        return {}
    func_pos = func_def_match.start()

    # select the closest comment before function
    selected_comment = None
    last_pos = -1
    for pos, comment in comment_blocks:
        if pos < func_pos and pos > last_pos:
            last_pos = pos
            selected_comment = comment

    if not selected_comment:
        return {}

    cb = selected_comment
    ensures_dict = {}
    auto_index = 1

    # iterate through occurrences of 'ensures' in the comment block using scanning
    for m in re.finditer(r"ensures\b", cb):
        abs_start = m.end()
        # note: scan_clause_from assumes absolute index in original text, so compute absolute
        # we can supply cb-relative scanning by offsetting indices or simply call scan on cb substring
        clause, _ = scan_clause_from(cb, abs_start)
        if clause is None:
            continue
        # clause may start with label like 'e_1:' or 'label:'
        lab_m = re.match(r"\s*([A-Za-z0-9_]+)\s*:\s*(.*)", clause, re.DOTALL)
        if lab_m:
            label = lab_m.group(1)
            body = lab_m.group(2).strip()
        else:
            label = str(auto_index)
            body = clause.strip()
            auto_index += 1
        # normalize whitespace
        body = re.sub(r"\s+", " ", body)
        ensures_dict[label] = body

    return ensures_dict


# ---------- 简单示例测试 ----------
if __name__ == "__main__":
    # test LLM style with quantifier
    text1 = r"""
    loop invariant \forall integer k; 0 <= k < i ==> max >= a[k];
    loop invariant i >= 0;
    """
    print("text1 ->", extract_loop_invariants_text(text1))

    text2 = r"""
    [Loop A]
    loop invariant \forall integer k; 
        0 <= k < i ==> max >= a[k];
    loop invariant i >= 0;

    [Loop B]
    loop invariant sum >= 0;
    """
    print("text2 ->", extract_loop_invariants_text(text2))

    # test ensures from code
    code = r"""
    /*@
      requires ...
      ensures e_1: \forall integer k; 0 <= k <= W ==> dp[0][k] == 0;
      ensures e_2: some_prop;
    */
    int _knapsnack(...) { ... }
    """
    print("ensures ->", extract_function_ensures_from_code(code, "_knapsnack"))
