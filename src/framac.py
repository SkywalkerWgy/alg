import os, io, sys, time, re
import logging
import subprocess
import datetime
import shlex
from typing import List

Check_STDOUT = 1                    # Set 1 if you want to record std result
Check_STDERR = 1                    # Set 1 if you want to record err result
SubprocessTimeout = 500             # Set the timeout of subprocess


# create subprocess according to the value of Check_STDOUT and Check_STDERR
def create_FRAMAC_subprocess(FRAMAC_Command, Check_STDOUT, Check_STDERR):
    # Create the FRAMAC command
    # Check_STDOUT and Check_STDERR are used to check the standard output and error of the FRAMAC subprocess
    if (Check_STDOUT == 1 and Check_STDERR == 1):
        process = subprocess.Popen(FRAMAC_Command, close_fds=True, preexec_fn=os.setpgrp, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    elif (Check_STDOUT == 1 and Check_STDERR == 0):
        process = subprocess.Popen(FRAMAC_Command, close_fds=True, preexec_fn=os.setpgrp, stdout=subprocess.PIPE)
    elif (Check_STDOUT == 0 and Check_STDERR == 1):
        process = subprocess.Popen(FRAMAC_Command, close_fds=True, preexec_fn=os.setpgrp, stderr=subprocess.PIPE)
    else:
        process = subprocess.Popen(FRAMAC_Command, close_fds=True, preexec_fn=os.setpgrp)
    return process


def get_result_type(context_bytes):
    # Convert from bytes to a list of strings (split by newline characters).
    result_type = "UK"
    try:
        context_strings = context_bytes.decode("utf-8")
        context_io = io.StringIO(context_strings)
        context = context_io.readlines()
    except:
        return result_type
    
    # Iterate through each line in the context.
    timeout_in_requires = 0
    for line in context:
        # If the line contains the string "[kernel] Frama-C aborted:", then the
        # build is invalid.
        if "[kernel] Frama-C aborted:" in line or "[kernel] Plug-in wp aborted" in line or "[wp] Warning: No goal generated" in line or "error: invalid preprocessing directive" in line:
            result_type = "Invalid"
            break
        elif "[wp] [Timeout] typed_" in line and ("_requires (" in line or "_requires_" in line):
            timeout_in_requires += 1
            continue
        # If the line contains the string "[wp] Proved goals:", then the build
        # is valid. The number of proved goals is given in the form "x/y",
        # where x is the number of proved goals and y is the number of total
        # goals. If x == y, then the build is a pass. Otherwise, the build is
        # a fail.
        elif "[wp] Proved goals:" in line:
            proportion = line.split(":")[-1]
            left, right = proportion.split("/")
            left = left.strip()
            right = right.strip()
            if int(left) + int(timeout_in_requires) == int(right):
                result_type = "Pass_" + left + "_" + right
            else:
                result_type = "Fail_" + left + "_" + right
            break

    return result_type

def run_framac_with_wp(Output_folder, gfile, time_out = 10):
    starttime = datetime.datetime.now()
    # FRAMAC_Command = ["frama-c", "-wp", "-wp-prop='-@terminates,-@lemma'", "-wp-print", "-wp-prover", "alt-ergo,z3,cvc4", "-wp-timeout", str(time_out), os.path.join(Output_folder, gfile)]
    FRAMAC_Command = shlex.split("frama-c -wp -wp-prop=\'-@terminates, -@lemma\' -wp-print -wp-prover alt-ergo,z3,cvc4 -wp-timeout 10 " + os.path.join(Output_folder, gfile))
    
    # create subprocess according to the value of check_STDOUT and check_STDERR
    process = create_FRAMAC_subprocess(FRAMAC_Command, Check_STDOUT, Check_STDERR)
    logging.info("[CMD] Running `" + ' '.join(FRAMAC_Command) + "`")

    output_std_file_name = ""
    output_err_file_name = ""
    output_result_type = ""
    try:
        # join subprocess
        if Check_STDOUT == 1 or Check_STDERR == 1:
            stdoutdata, stderrdata = process.communicate(timeout=SubprocessTimeout)
            fleft, fright = gfile.split(".")
            fright = "." + fright
            if stdoutdata != b'':
                result_type = get_result_type(stdoutdata)
                output_result_type = result_type
                fleft = fleft.replace("_gen_", "_fstd_")
                fstd_file_name = fleft + "_" + result_type
                output_std_file_name = os.path.join(Output_folder, fstd_file_name + ".txt")
                with open (output_std_file_name, "wb") as stdfile:
                    #stdfile.write(bytes(str(pattern)+"\n", encoding = "utf8"))
                    stdfile.write(stdoutdata)
            if stderrdata != b'':
                fleft = fleft.replace("_gen_", "_ferr_")
                output_err_file_name = os.path.join(Output_folder, fleft + ".txt")
                with open (output_err_file_name, "wb") as errfile:
                    errfile.write(stderrdata)
        else:
            process.communicate(timeout=SubprocessTimeout)
    
    except subprocess.TimeoutExpired:
        # process.kill()
        # process.terminate()
        subprocess.check_call(["sudo", "kill", str(process.pid)])
        #os.waitpid(process.pid, 0)
        logging.error("Timeout for subprocess when running frama-c on" + ' '.join(os.path.join(Output_folder, gfile)))
    
    except Exception as e:
        print("\033[34m\tUnknown Exception" + "\033[0m")
        print(e)
        raise e
    endtime = datetime.datetime.now()
    solve_time = endtime - starttime
    return output_result_type, output_std_file_name, output_err_file_name, solve_time

def parse_frama_valid_output(log_text: str) -> dict:
    result = {}

    pattern_est = re.compile(
        r"\[wp\]\s*\[(?:Timeout|Unknown)\]\s*typed_[\w]+_loop_invariant_(i_\d+)_established", re.I
    )

    pattern_pre = re.compile(
        r"\[wp\]\s*\[(?:Timeout|Unknown)\]\s*typed_[\w]+_loop_invariant_(i_\d+)_preserved", re.I
    )

    pattern_ens = re.compile(
        r"\[wp\]\s*\[(?:Timeout|Unknown)\]\s*typed_[\w]+_ensures_(e_\d+)", re.I
    )

    # ★ 新增：assert 未证明成功
    pattern_assert = re.compile(
        r"\[wp\]\s*\[(?:Timeout|Unknown)\]\s*typed_[\w]+_assert_(a_\d+)", re.I
    )

    # loop invariant establishment
    for m in pattern_est.finditer(log_text):
        result[m.group(1)] = "establishment"

    # loop invariant preservation
    for m in pattern_pre.finditer(log_text):
        if m.group(1) in result and result[m.group(1)] == "establishment":
            result[m.group(1)] = "both"
        else:
            result[m.group(1)] = "preservation"

    # ensures failure
    for m in pattern_ens.finditer(log_text):
        result[m.group(1)] = False

    # ★ assert failure（等价于 ensures failure）
    for m in pattern_assert.finditer(log_text):
        result[m.group(1)] = False

    return result


def parse_frama_invalid_output(c_code: str, log_text: str):
    to_delete = {}

    if "Frama-C aborted: invalid user input" not in log_text:
        return to_delete

    annot_pattern = re.compile(
        r":\s*(\d+)\s*:\s*Warning:[\s\S]{0,400}?Ignoring loop annotation",
        flags=re.IGNORECASE
    )
    error_line_strings = annot_pattern.findall(log_text)
    error_lines = sorted({int(x) for x in error_line_strings})  

    if not error_lines:
        wide_pat = re.compile(r"\[kernel:annot-error\][\s\S]{0,500}?:\s*(\d+)\s*:\s*", re.I)
        found = wide_pat.findall(log_text)
        if found:
            error_lines = sorted({int(x) for x in found})

    if not error_lines:
        return to_delete

    inv_pat = re.compile(
        r"(loop\s+invariant\s+(?P<id>i_\d+)\s*:\s*(?P<body>.*?);)",
        flags=re.IGNORECASE | re.S
    )

    invariants = [] 
    for m in inv_pat.finditer(c_code):
        full_text = m.group(1).strip()
        inv_id = m.group("id")
        start_idx = m.start(1)
        end_idx = m.end(1)
        start_line = c_code[:start_idx].count("\n") + 1
        end_line = c_code[:end_idx].count("\n") + 1
        invariants.append((inv_id, full_text, start_line, end_line))

    for err_line in error_lines:
        for inv_id, full_text, sline, eline in invariants:
            if sline <= err_line <= eline:
                to_delete[inv_id] = full_text

    return to_delete


if __name__ == "__main__":
    with open('../output_fail_3.txt', 'r') as f: 
        log = f.read()
    print(log)
    res = parse_frama_valid_output(log)
    print(res)
    c_code = open("/home/wgy/algorithms/Result/acsl-algorithms/_min_seq.c/_min_seq_verified_1.c", "r", encoding="utf-8").read()
    log_text = open("/home/wgy/algorithms/Result/acsl-algorithms/_min_seq.c/_min_seq_verified_1_Fail_16_17.txt", "r", encoding="utf-8").read()
    print(c_code)
    print(log_text)
    del_map = parse_frama_invalid_output(c_code, log_text)
    print(del_map)
    for k,v in del_map.items():
        print(k, v)