import os
import re

def count_loops_in_folder(folder_path, exts=(".c", ".h")):
    """
    统计 folder_path 下每个文件中 for / while 循环的数量

    返回:
        dict: { filename : loop_count }
    """

    loop_pattern = re.compile(r'\b(for|while)\s*\(')

    def remove_comments(code: str) -> str:
        # 移除 // 注释
        code = re.sub(r'//.*', '', code)
        # 移除 /* */ 注释（支持多行）
        code = re.sub(r'/\*.*?\*/', '', code, flags=re.S)
        return code

    result = {}

    for root, _, files in os.walk(folder_path):
        for fname in files:
            if not fname.endswith(exts):
                continue

            path = os.path.join(root, fname)

            try:
                with open(path, "r", encoding="utf-8", errors="ignore") as f:
                    code = f.read()
            except Exception as e:
                print(f"[Warning] Cannot read {path}: {e}")
                continue

            code = remove_comments(code)

            loops = loop_pattern.findall(code)
            result[path] = len(loops)

    return result


folder = "OOPSLA"
loop_counts = count_loops_in_folder(folder)

# for file, cnt in loop_counts.items():
#     print(f"{file}: {cnt}")

files_gt_1 = [f for f, v in loop_counts.items() if v > 1]
print(len(files_gt_1))
print(files_gt_1)


