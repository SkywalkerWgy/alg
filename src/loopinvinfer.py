import os
import queue
import re
import sys
import time
import argparse
import logging
import framac
import processor
import shutil
# from transformers import AutoModelForCausalLM, AutoTokenizer
# from transformers import GenerationConfig


def verify(code, file_basename, logpath, logger, maxtime, tokenizer=None, pangumodel=None):
    check = False
    trytime = 1
    proposal = 0
    invalidtime = 0

    # -------------------------------
    # Initialize the loop processor
    # -------------------------------
    loops = processor.build_loops(code, file_basename, model, logger)
    loops.initial_loop_invariant_inference()

    # -------------------------------
    # First phase (bounded attempts)
    # -------------------------------
    while not check and trytime <= maxtime:

        
        loops.logger_inv()
        code_with_inv = loops.inject_invariants()

        logger.info("----------Code with Invariants----------")
        logger.info(code_with_inv)
        logger.info("----------------------------------------")

        out_c_file = os.path.join(logpath, f"{file_basename}_verified_{trytime}.c")
        with open(out_c_file, "w", encoding="utf-8") as f:
            f.write(code_with_inv)

        proposal += 1

        output_result_type, out_std, out_err, solve_time = \
            framac.run_framac_with_wp(logpath, os.path.basename(out_c_file))

        # read WP result
        with open(out_std, 'r') as f:
            log = f.read()

        # ---------- Case: Invalid ----------
        if output_result_type == "Invalid":
            invalid_msg = framac.parse_frama_invalid_output(code_with_inv, log)
            for k in invalid_msg:
                loops.remove_invariant_by_id(k)
            invalidtime += 1
            if invalidtime > 10:
                return "", proposal, False


        # ---------- Case: Fail_k ----------
        elif output_result_type.startswith("Fail_"):
            logger.info("----------Begin Revise----------")

            error_msg = framac.parse_frama_valid_output(log)
            print(error_msg)

            for k, v in error_msg.items():
                if k.startswith("e") or k.startswith("a"):
                    loops.revise_loop_invariant_inference(k, loops.ensures[k])
                elif k.startswith("i"):
                    loops.update_error_count(k)
                    if loops.error_count[k] > 5:
                        loops.remove_invariant_by_id(k)
                        continue
                    loops.revise_loop_invariant_inference(k, v)

            logger.info("--------------------------------")
            trytime += 1

        # ---------- Case: Pass ----------
        elif output_result_type.startswith("Pass_"):
            return code_with_inv, proposal, True

        # ---------- Unknown ----------
        else:
            logger.error(f"Unknown Frama-C result: {output_result_type}")
            return "", proposal, False

    # -------------------------------------------------------------
    # Second phase (aggressive removal / final attempts)
    # -------------------------------------------------------------
    while True:

        loops.logger_inv()
        code_with_inv = loops.inject_invariants()

        logger.info("----------Code with Invariants----------")
        logger.info(code_with_inv)
        logger.info("----------------------------------------")

        out_c_file = os.path.join(logpath, f"{file_basename}_verified_final_attempt_{trytime}.c")
        with open(out_c_file, "w", encoding="utf-8") as f:
            f.write(code_with_inv)

        proposal += 1

        output_result_type, out_std, out_err, solve_time = \
            framac.run_framac_with_wp(logpath, os.path.basename(out_c_file), 10)

        with open(out_std, 'r') as f:
            log = f.read()

        # ---------- Case: Invalid ----------
        if output_result_type == "Invalid":
            invalid_msg = framac.parse_frama_invalid_output(code_with_inv, log)
            for k in invalid_msg:
                loops.remove_invariant_by_id(k)

        # ---------- Case: Fail ----------
        elif output_result_type.startswith("Fail_"):
            error_msg = framac.parse_frama_valid_output(log)
            print(error_msg)

            terminate = True
            for k, v in error_msg.items():
                if k.startswith("i"):
                    terminate = False

                loops.update_error_count(k)
                loops.remove_invariant_by_id(k)

            if terminate:
                return "", proposal, False

            trytime += 1

        # ---------- Case: Pass ----------
        elif output_result_type.startswith("Pass_"):
            return code_with_inv, proposal, True

        else:
            logger.error(f"Unknown Frama-C result: {output_result_type}")
            return "", proposal, False

    return "", proposal, False

def verify_ablation(code, file_basename, logpath, logger, maxtime, tokenizer=None, pangumodel=None):
    check = False
    trytime = 1
    proposal = 0

    # -------------------------------
    # Initialize loop processor
    # -------------------------------
    loops = processor.build_loops(code, file_basename, model, logger)

    while trytime <= 5 and not check:

        logger.info(f"========== Attempt {trytime} ==========")

        # ---------------------------------
        # Initial loop invariant inference
        # ---------------------------------
        loops.initial_loop_invariant_inference()

        loops.logger_inv()
        code_with_inv = loops.inject_invariants()

        logger.info("---------- Code with Invariants ----------")
        logger.info(code_with_inv)
        logger.info("------------------------------------------")

        out_c_file = os.path.join(
            logpath, f"{file_basename}_verified_{trytime}.c"
        )
        with open(out_c_file, "w", encoding="utf-8") as f:
            f.write(code_with_inv)

        proposal += 1

        output_result_type, out_std, out_err, solve_time = \
            framac.run_framac_with_wp(
                logpath, os.path.basename(out_c_file)
            )

        # Read WP output
        with open(out_std, "r") as f:
            log = f.read()

        # -------------------------------
        # Case: Pass
        # -------------------------------
        if output_result_type.startswith("Pass_"):
            logger.info("Verification succeeded.")
            return code_with_inv, proposal, True

        # -------------------------------
        # Case: Not Pass → reset and retry
        # -------------------------------
        else:
            logger.info(
                f"Verification failed ({output_result_type}), "
                "removing all invariants and retrying."
            )

            # loops.remove_all_invariants()
            trytime += 1

    logger.info("Verification failed: reached maximum attempts.")
    return "", proposal, False


import os
import re
from statistics import mean

import os
import re
from statistics import mean

def analyze_logs(root_dir, analysis_all=False):
    # 默认的三个数据集目录名称
    DATASETS = ['OOPSLA', 'SVCOMP', 'acsl-algorithms']
    
    # 定义待扫描的路径列表
    target_dirs = []

    if analysis_all:
        print(f"[*] Analysis Mode: ALL DATASETS (Global Aggregation)")
        print(f"[*] Base path provided: {root_dir}")
        
        # 1. 确定当前 root_dir 包含哪个数据集名称
        # 我们需要找到 root_dir 里包含了 DATASETS 中的哪一个，以便进行替换
        # 使用 os.path.normpath 去掉末尾可能存在的 '/'，防止匹配出错
        norm_path = os.path.normpath(root_dir)
        
        current_ds_name = None
        for ds in DATASETS:
            # 注意：这里判断路径中是否包含数据集名称
            # 为了防止部分匹配（例如 path/to/NOT_OOPSLA/），最好结合目录分隔符判断，
            # 但通常简单的字符串包含在你的目录结构下是够用的。
            if ds in norm_path:
                current_ds_name = ds
                break
        
        if current_ds_name:
            # 2. 生成所有数据集的路径
            for ds in DATASETS:
                # 将当前路径中的数据集名称替换为目标数据集名称
                # 例如: ".../OOPSLA/GPT4" -> ".../SVCOMP/GPT4"
                new_path = root_dir.replace(current_ds_name, ds)
                
                if os.path.exists(new_path):
                    target_dirs.append(new_path)
                else:
                    print(f"[Warning] Path not found, skipping: {new_path}")
        else:
            print(f"[Error] Could not identify dataset name in path: {root_dir}")
            print(f"Expected one of: {DATASETS}")
            return
    else:
        # 如果不是 analysis_all，就只分析传进来的这一个目录
        if os.path.exists(root_dir):
            target_dirs.append(root_dir)
        else:
            print(f"[Error] Directory not found: {root_dir}")
            return

    # ================= 收集日志 =================
    log_results = []   # [(problem_name, success, running_time, proposal_number)]
    
    print(f"[*] Scanning directories: {len(target_dirs)}")
    for target_dir in target_dirs:
        # print(f"    -> {target_dir}") # 调试用，可以取消注释
        for dirname, subdirs, files in os.walk(target_dir):
            if "log.log" not in files:
                continue

            log_path = os.path.join(dirname, "log.log")
            problem_name = os.path.basename(dirname)

            try:
                with open(log_path, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()
            except Exception as e:
                # print(f"[Warning] Cannot read {log_path}: {e}")
                continue

            idx = content.rfind("---------Result---------")
            if idx == -1:
                continue

            result_block = content[idx:]

            m_status = re.search(r"^(Success|Fail)", result_block, re.MULTILINE)
            if not m_status:
                continue
            is_success = (m_status.group(1) == "Success")

            m_rt = re.search(r"Running time\s*:\s*([0-9.]+)", result_block)
            if not m_rt:
                continue
            running_time = float(m_rt.group(1))

            m_prop = re.search(r"Proposal number\s*:\s*([0-9]+)", result_block)
            if not m_prop:
                continue
            proposal_number = int(m_prop.group(1))

            log_results.append(
                (problem_name, is_success, running_time, proposal_number)
            )

    if not log_results:
        print("No valid log results found in the specified paths.")
        return

    # ================= 统计函数 =================
    def calculate_statistics(logs):
        success_cases = [x for x in logs if x[1]]
        fail_cases = [x for x in logs if not x[1]]

        success_count = len(success_cases)
        # 避免除以零
        avg_runtime = mean(x[2] for x in success_cases) if success_cases else 0.0
        avg_proposal = mean(x[3] for x in success_cases) if success_cases else 0.0

        sum_runtime = sum(x[2] for x in success_cases) if success_cases else 0.0
        sum_proposal = sum(x[3] for x in success_cases) if success_cases else 0.0
        
        success_names = [x[0] for x in success_cases]
        fail_names = [x[0] for x in fail_cases]

        return success_count, success_names, fail_names, avg_runtime, avg_proposal, sum_runtime, sum_proposal

    def print_statistics(label, stats, total_parsed):
        success_count, success_names, fail_names, avg_runtime, avg_proposal, sum_runtime, sum_proposal = stats
        print(f"\n----- {label} -----")
        print(f"Total logs parsed   : {total_parsed}")
        print(f"Success count       : {success_count}")
        # print(f"Success problems    : {success_names}") 
        print(f"Avg running time    : {avg_runtime:.4f}")
        print(f"Avg proposal number : {avg_proposal:.2f}")
        print(f"Sum running time    : {sum_runtime:.4f}")
        print(f"Sum proposal number : {sum_proposal}")
        rate = (success_count / total_parsed * 100) if total_parsed > 0 else 0
        print(f"Success Rate        : {rate:.2f}%")

    # ================= 输出结果 =================
    
    if analysis_all:
        # 模式1：汇总统计所有数据集
        all_stats = calculate_statistics(log_results)
        # 获取当前模型名称 (从 root_dir 提取最后一部分)
        model_name = os.path.basename(os.path.normpath(root_dir))
        print_statistics(f"GLOBAL STATISTICS (Model: {model_name})", all_stats, len(log_results))
        
    
    # 模式2：原有的 Nested/Not Nested 分类统计 (仅针对单个 Dataset)
    
    # 你的 nested 列表定义
    list1 = ['OOPSLA/oopsla_27.c', 'OOPSLA/oopsla_03.c', 'OOPSLA/oopsla_09.c', 'OOPSLA/oopsla_29.c', 
                'OOPSLA/oopsla_40.c', 'OOPSLA/oopsla_24.c', 'OOPSLA/oopsla_33.c', 'OOPSLA/oopsla_45.c', 
                'OOPSLA/oopsla_06.c', 'OOPSLA/oopsla_31.c', 'OOPSLA/oopsla_12.c', 'OOPSLA/oopsla_17.c', 
                'OOPSLA/oopsla_28.c', 'OOPSLA/oopsla_26.c', 'OOPSLA/oopsla_36.c', 'OOPSLA/oopsla_25.c']
    list2 = ['SVCOMP/svcomp_16.c', 'SVCOMP/svcomp_21.c', 'SVCOMP/svcomp_14.c', 'SVCOMP/svcomp_18.c', 
                'SVCOMP/svcomp_15.c', 'SVCOMP/svcomp_10.c', 'SVCOMP/svcomp_17.c', 'SVCOMP/svcomp_9.c']
    list3 = ['acsl-algorithms/_trap_rain.c', 'acsl-algorithms/_select_sort.c', 'acsl-algorithms/_count.c', 
                'acsl-algorithms/_knapsnack.c', 'acsl-algorithms/_lis.c', 'acsl-algorithms/_bfs.c', 
                'acsl-algorithms/_partition_hoare.c', 'acsl-algorithms/_prefix_function.c', 
                'acsl-algorithms/_naive_string_matcher.c', 'acsl-algorithms/_lcs.c', 'acsl-algorithms/_dfs.c', 
                'acsl-algorithms/_bubble_sort.c', 'acsl-algorithms/_merge.c', 'acsl-algorithms/_rod_cutting_dp.c', 
                'acsl-algorithms/_huffman.c', 'acsl-algorithms/_edit_distance.c', 'acsl-algorithms/_bellmanford.c', 
                'acsl-algorithms/_longest_palindrome_subseq.c', 'acsl-algorithms/_compute_prefix_function.c', 
                'acsl-algorithms/_matrix_chain.c', 'acsl-algorithms/_insertion_sort.c']

    nested = list1 + list2 + list3

    in_nested = [x for x in log_results if any(x[0] in file for file in nested)]
    not_in_nested = [x for x in log_results if all(x[0] not in file for file in nested)]

    in_nested_stats = calculate_statistics(in_nested)
    not_in_nested_stats = calculate_statistics(not_in_nested)

    print_statistics("In Nested", in_nested_stats, len(in_nested))
    print_statistics("Not In Nested", not_in_nested_stats, len(not_in_nested))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", default='_min_seq.c', type=str)
    parser.add_argument("--output", default='../Result/', type=str)
    parser.add_argument("--model", default="openai/gpt-5.1", type=str)
    parser.add_argument("--proposal", default=10, type=int)
    parser.add_argument("--dataset", default='acsl-algorithms', type=str)

    parser.add_argument("--analysis", action="store_true")
    parser.add_argument("--runAll", action="store_true")
    parser.add_argument("--ablation", action="store_true")
    parser.add_argument("--analysisall", action="store_true")

    args = parser.parse_args()

    if args.ablation:
        args.output = '../ResultAblation/'
        
    maxtime = args.proposal
    model = args.model

    if "openPangu" in args.model and args.analysis is False and args.analysisall is False:
        model_local_path = "/opt/pangu/" + args.model

        tokenizer = AutoTokenizer.from_pretrained(
            model_local_path, 
            use_fast=False, 
            trust_remote_code=True,
            local_files_only=True
        )
        pangumodel = AutoModelForCausalLM.from_pretrained(
            model_local_path,
            trust_remote_code=True,
            torch_dtype="auto",
            device_map="npu",
            local_files_only=True
        )
        
    else:
        tokenizer = None
        pangumodel = None
    # ------------------------------------------------
    # -------- Helper: prepare logger per file -------
    # ------------------------------------------------
    def build_logger(logfile: str):
        """
        Build an isolated logger for each file.
        Ensures no handler contamination from previous files.
        """
        logger = logging.getLogger('loopinvinfer')

        # Clear old handlers
        if logger.hasHandlers():
            for h in logger.handlers[:]:
                logger.removeHandler(h)
                h.close()

        logger.setLevel(logging.DEBUG)

        # Init log file
        with open(logfile, 'w') as f:
            f.truncate()

        # Add new handlers
        fh = logging.FileHandler(logfile)
        fh.setLevel(logging.DEBUG)
        sh = logging.StreamHandler()
        sh.setLevel(logging.DEBUG)

        logger.addHandler(fh)
        logger.addHandler(sh)

        return logger

    # ------------------------------------------------
    # -------- Helper: process one file --------------
    # ------------------------------------------------
    def process_file(fname: str):
        """
        Process one .c file: build logger, read code, verify, save results.
        """

        codepath = '../Benchmark/' + args.dataset +'/' + fname
        log_dir = os.path.join(args.output, args.dataset, model, fname)

        # Rebuild directory
        if os.path.exists(log_dir):
            return
        os.makedirs(log_dir)

        logfile = os.path.join(log_dir, "log.log")
        logger = build_logger(logfile)
        
        if "openPangu" in args.model:
            logger.info("-----------Model-----------")
            logger.info("Model type:")
            logger.info(str(pangumodel))
            logger.info("Model device:")
            logger.info(str(pangumodel.device))
            logger.info("---------------------------")
        else: 
            logger.info("-----------Model-----------")
            logger.info("Model type:")
            logger.info(str(model))
            logger.info("---------------------------")
        # Log the code
        logger.info("File Path: " + codepath)
        with open(codepath, 'r') as f:
            code = f.read()

        logger.info("----------Code----------")
        logger.info(code)
        logger.info("------------------------")

        t_start = time.time()
        if args.ablation:
            verified_code, number_attempts, result = verify_ablation(
                code=code,
                file_basename=fname.split('.')[0],
                logpath=log_dir,
                logger=logger,
                maxtime=maxtime,
                tokenizer=tokenizer, 
                pangumodel=pangumodel
            )
        else:
            verified_code, number_attempts, result = verify(
                code=code,
                file_basename=fname.split('.')[0],
                logpath=log_dir,
                logger=logger,
                maxtime=maxtime,
                tokenizer=tokenizer, 
                pangumodel=pangumodel
            )
        t_finish = time.time()

        # Store all results
        logger.info("---------Result---------")
        logger.info("Success" if result else "Fail")
        logger.info(f"Model: {model}")
        logger.info(f"Running time: {t_finish - t_start}")
        logger.info(f"Proposal number: {number_attempts}")
        logger.info("Verified code:")
        logger.info(verified_code)
        logger.info("------------------------")

    # ------------------------------------------------
    # ----------- ANALYSIS MODE ----------------------
    # ------------------------------------------------
    if args.analysis or args.analysisall:
        print("Running log analysis...")
        analyze_logs(args.output + args.dataset + '/' + args.model + '/', args.analysisall)
        sys.exit(0)

    # ------------------------------------------------
    # ------ RUN ALL FILES IN DIRECTORY --------------
    # ------------------------------------------------
    if args.runAll:
        DATASETS = ['OOPSLA', 'SVCOMP', 'acsl-algorithms']
        for dataset in DATASETS:
            args.dataset = dataset
            base = f'../Benchmark/{args.dataset}/'
            for fname in os.listdir(base):
                if fname.endswith(".c"):
                    process_file(fname)
            print("\n>>> All algorithms processed.")
            
        sys.exit(0)
    # ------------------------------------------------
    # -------------- RUN SINGLE FILE -----------------
    # ------------------------------------------------
    process_file(args.file)