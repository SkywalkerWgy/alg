from loop import Loop
import string

sys_prompt = """
You are an expert in ACSL-based deductive program verification (Frama-C).  
Your job is to generate **only loop invariants** (ACSL `loop invariant` clauses), depending on the task type:

1. **Initial Invariant Inference**  
   - Insert invariants at the hint.  
   - Consider zero-iteration and normal termination cases.  
   - Include any preconditions that are also invariants.  
   - Output only:
     loop invariant ...;

2. **Strengthening for Unproved Ensures**  
   - Add only the *new* invariants needed for the failed ensures clause.  
   - Do not repeat existing invariants.  
   - Output only the new invariants.

3. **Weaken Invariant (Establishment Failure)**  
   - Relax only the invariant(s) that cannot be established.  
   - Do not restate existing invariants.

4. **Cross-Loop Establishment Fix**  
   - Modify invariants of the preceding loop, current loop, or both.  
   - Output in two blocks:
     [Loop <PRE_LOOP>]
     loop invariant ...;

     [Loop <CUR_LOOP>]
     loop invariant ...;

5. **Nested Preservation Fix**  
   - Modify invariants of the inner loop, outer loop, or both.  
   - Output in two blocks:
     [Loop <INNER_LOOP>]
     loop invariant ...;

     [Loop <CUR_LOOP>]
     loop invariant ...;

6. **Self Preservation Fix**  
   - Add or adjust invariants so the loop invariant becomes inductive.  

RULES:  
- **Output only ACSL loop invariants**, no explanation.  
- **Never restate original invariants unless modifying them**.  
- **All invariants must satisfy establishment, preservation, and zero-iteration validity**.  
- Use ACSL syntax: &&, ||, ==> , \\forall, \\exists, etc.  
"""

prompt_template_initial_reasoning = """
<The code I give you>
You are an expert in program verification, and please generate loop invariant as C annotation comments at the hint location \
(annotated by "[Hint] Please infer the loop invariant for the following loop.") using ACSL language.
ACSL is a specification language for C programs that conforms to the design by contract paradigm, utilizing Hoare style pre- and postconditions and invariants. \
Note that the `loop invariant` clause is a condition that is true at the beginning and end of every loop iteration.
Specifically, for the current verification task:
    - Pre-condition: <PRECONDITION>
    - Post-condition: <POSTCONDITION>
Please verify that the generated loop invariant is consistent with these constraints. \
If these specific pre- or post-conditions are not provided or empty, please infer the loop invariant strictly based on the program's execution logic and standard correctness.
In order to get a correct answer, You may want to consider both the situation of not entering the loop and the situation of jumping out of the loop. \
If some of the pre-conditions are also loop invariant, you need to add them to your answer as well.
Use '&&', '||', '==>', '\\forall' or '\\exists' if necessary. For instance:
```
loop invariant 1 <= x;
loop invariant x == y;
loop invariant 0 < x ==> y <= z;
loop invariant z % 2 == 1 || x == y;
loop invariant z % 2 == 1 && x <= y;
loop invariant \\forall integer k;  0 <= k < i ==> max >=  a[k];
loop invariant \\exists integer k;  0 <= k < i &&  max == a[k];
```
Your answer should follow the following format:
```
loop invariant ...;
loop invariant ...;
...
```
No explanation. No commentary. Just show me the loop invariant.
"""


prompt_template_initial_reasoning_ablation = """
<The code I give you>
You are an expert in program verification, and please generate loop invariant as C annotation comments at the hint location \
(annotated by "[Hint] Please infer the loop invariant for the following loop.") using ACSL language.
ACSL is a specification language for C programs that conforms to the design by contract paradigm, utilizing Hoare style pre- and postconditions and invariants. \
Note that the `loop invariant` clause is a condition that is true at the beginning and end of every loop iteration.\
The pre- and post-conditions of functions are written as `requires` and `ensures` clauses, respectively.
Use '&&', '||', '==>', '\\forall' or '\\exists' if necessary. For instance:
```
loop invariant 1 <= x;
loop invariant 0 < x ==> y <= z;
loop invariant z % 2 == 1 || x == y;
loop invariant \\forall integer k;  0 <= k < i ==> max >=  a[k];
```
Your answer should follow the following format:
```
loop invariant ...;
loop invariant ...;
...
```
No explanation. No commentary. Just show me the loop invariant.
"""

prompt_template_ensure = """
<The code I give you>
You are an expert in deductive program verification using ACSL and Frama-C. Your task is to fix a verification failure by providing the necessary loop invariants.
The verification failed with the following error regarding an 'ensures' clause:
[Unproved Ensures]  <ERROR_MSG_HERE>
The verification failure is caused exclusively by the weakness of the loop invariant in <LOOP_ALPHABET>. It fails to capture enough state information to imply the postcondition upon loop termination.
   - There is a logical gap between what is known when the loop ends (the current invariant + negated loop condition) and what is required by the ensures clause.
   - Remedy: You must add new invariant clauses only at the location marked by "[Hint] Please strengthen the loop invariant in the following loop". These new clauses must be strong enough to imply the specific properties mentioned in the failed ensures clause. If some of the pre-conditions are also loop invariant, you need to add them to your answer as well.
IMPORTANT RULES:
1. Your answer should follow the following format:
   ```
   loop invariant ...;
   loop invariant ...;
   ...
   ```
   All invariants must strictly satisfy ACSL rules.
2. Do not output any of the original invariants. Only output the new or modified invariant you propose.
3. No explanation. No commentary. Just show me the loop invariant.
"""

prompt_template_establishment_requires = """
<The code I give you>
You are an expert in deductive program verification using ACSL and Frama-C.
The following loop invariant of the loop labeled "<LOOP_ALPHABET>" cannot be established from the function's `requires` clauses:
[Unprovable Initial Invariant] <ERROR_MSG_HERE>
This means the loop invariant is too strong at the loop entry, violating the establishment condition of loop correctness.  
Your task is to relax or weaken the loop invariant at the position marked by: "[Hint] Loop invariant too strong initially. Relax it."
IMPORTANT RULES:
1. The relaxed invariants must still hold:
   - Establishment: They must be provable solely from the function's requires clauses and the program state before entering the loop.
   - Preservation: after executing the loop body exactly once, the invariant still holds.
   - Zero-iteration case: the invariant is valid even if the loop never executes.
2. Do NOT restate or print any of the existing loop invariants.  
   Only output the modified (weakened) invariants necessary to make the establishment step succeed.
3. Your answer must be solely in the form:
   ```
   loop invariant ...;
   loop invariant ...;
   ...
   ```
4. All invariants must follow ACSL syntax and be valid loop invariants.
5. No explanation. No commentary. Just show me the loop invariant.
"""

prompt_template_establishment_cross = """
<The code I give you>
You are an expert in deductive program verification using ACSL and Frama-C.
[Unprovable Invariant] <ERROR_MSG_HERE>
The above loop invariant required by the loop labeled "<CUR_LOOP>" cannot be derived from the invariants of the preceding loop "<PRE_LOOP>", and the program state before entering the current loop:
[Pre-statement]
<PRE_STATE>
Accordingly, we must fix the situation that prevents proving the current loop invariant. There are two independent possibilities you should consider and address:
  1) The current loop invariant for "Loop <CUR_LOOP>" is too strong:
     - It uses facts that are not guaranteed by the preceding loop invariants together with Pre-statement.
     - Remedy: weaken or simplify the invariant of "<CUR_LOOP>" so it becomes derivable from the available preconditions.

  2) The preceding loop invariants of "Loop <PRE_LOOP>" are too weak:
     - They do not imply the facts required by the "<CUR_LOOP>" invariant after executing Pre-statement.
     - Remedy: strengthen the invariant(s) of "Loop <PRE_LOOP>" so that, after running Pre-statement, they imply the needed facts for "Loop <CUR_LOOP>".

Your task is to adjust the invariants so that the establishment of "Loop <CUR_LOOP>" succeeds.
IMPORTANT RULES:
1. You may modify either:
   - only the current loop "<CUR_LOOP>", or  
   - only the preceding loop "<PRE_LOOP>", or  
   - both, if needed.
2. Do NOT output any of the original invariants.  
   Only output the new or modified invariants you propose.
3. Output must contain two blocks, even if one block is empty:
   ```
   [Loop <PRE_LOOP>]
   loop invariant ...;
   loop invariant ...;

   [Loop <CUR_LOOP>]
   loop invariant ...;
   loop invariant ...;
   ```
4. Each block may contain zero or more invariants. If a block has no changes, leave it empty but keep the block header.
5. All invariants must follow ACSL syntax and be valid loop invariants.
6. No explanation. No commentary. Just show me the loop invariant.
"""

prompt_template_preservation_nested = """
<The code I give you>
You are an expert in deductive program verification using ACSL and Frama-C.
[Unprovable Invariant] <ERROR_MSG_HERE>
The loop invariant of the loop labeled "<CUR_LOOP>" fails the *preservation* check. After one iteration of the loop body, the invariant cannot be re-established.
Accordingly, there are two distinct possibilities that may prevent the preservation of the current loop invariant:
  1) The unprovable invariant of "Loop <CUR_LOOP>" is incorrect:
     - It cannot be re-established from itself after executing the loop body.
     - Remedy: modify the unprovable invariant of "<CUR_LOOP>" so that it becomes inductive.

  2) The invariant(s) of the nested inner loop "Loop <INNER_LOOP>" are too weak:
     - They do not guarantee enough facts after the completion of the inner loop to re-establish "<CUR_LOOP>"'s invariant.
     - Remedy: strengthen the invariant(s) of "<INNER_LOOP>" so that the preservation of "<CUR_LOOP>" becomes provable.

Your task is to adjust the invariants so that the preservation of "Loop <CUR_LOOP>" succeeds.
IMPORTANT RULES:
1. You may modify either:
   - only the current loop "<CUR_LOOP>", or
   - only the inner loop "<INNER_LOOP>", or
   - both, if needed.
2. Do NOT output any of the original invariants. Only output the new or modified invariants you propose.
3. Output must contain two blocks, even if one block is empty:
   ```
   [Loop <INNER_LOOP>]
   loop invariant ...;
   loop invariant ...;

   [Loop <CUR_LOOP>]
   loop invariant ...;
   loop invariant ...;
   ```
4. Each block may contain zero or more invariants. If a block has no changes, leave it empty but keep the block header.
5. All invariants must strictly satisfy ACSL rules and must be valid inductive loop invariants.
6. No explanation. No commentary. Just show me the loop invariant.
"""

prompt_template_preservation_self = """
<The code I give you>
You are an expert in deductive program verification using ACSL and Frama-C.
[Unprovable Invariant] <ERROR_MSG_HERE>
The above loop invariant of loop "<LOOP_ALPHABET>" fails the preservation (inductive) condition:
after executing one iteration of the loop body, the invariant cannot be re-established.
[Loop Body]
<LOOP_BODY>
This failure indicates that the current invariant may be incorrect or incomplete.  
There are two typical causes:
  1) The invariant is logically incorrect, so it does not hold after the loop body executes once.
     - In this case, you must adjust the invariant so that it is preserved by the loop body.
  2) The invariant is insufficient, i.e., it misses essential supporting conditions needed to re-establish itself.
     - In this case, you must introduce additional invariants so that the whole set becomes inductive.
Your task is to produce the corrected and/or auxiliary invariants that make the preservation step succeed.
IMPORTANT RULES:
1. You MUST NOT output any of the original invariants already in the code. Only output the new or modified invariants.
2. All invariants you produce must satisfy:
   - Establishment: they hold on loop entry.
   - Preservation: after executing the loop body exactly once, the invariant still holds.
   - Zero-iteration case: the invariant is valid even if the loop never executes.
3. The answer must follow this format exactly:
   ```
   loop invariant ...;
   loop invariant ...;
   ...
   ```
4. All invariants must follow ACSL syntax and be valid loop invariants.
5. No explanation. No commentary. Just show me the loop invariant.
"""

def get_prompt(prompt_code, prompt_type: str, current_loop: Loop = None, error_msg = None, inner_loop: Loop = None, pre_condition: str = "", post_condition: str = ""):
    if prompt_type == "initial_reasoning":
        question = (
            prompt_template_initial_reasoning
            .replace("<The code I give you>", prompt_code)
            .replace("<PRECONDITION>", pre_condition)
            .replace("<POSTCONDITION>", post_condition)
        )
    elif prompt_type == "initial_reasoning_ablation":
        question = prompt_template_initial_reasoning_ablation.replace("<The code I give you>", prompt_code)
    elif prompt_type == "ensure":
        question = (
            prompt_template_ensure
            .replace("<The code I give you>", prompt_code)
            .replace("<ERROR_MSG_HERE>", error_msg)
            .replace("<LOOP_ALPHABET>", current_loop.alphabet)
        )
    elif prompt_type == "establishment_requires":
        question = (
            prompt_template_establishment_requires
            .replace("<The code I give you>", prompt_code)
            .replace("<ERROR_MSG_HERE>", error_msg)
            .replace("<LOOP_ALPHABET>", current_loop.alphabet)
        )
    elif prompt_type == "establishment_cross":
        pre_loop_alphabet = string.ascii_uppercase[current_loop.pre_loop] if current_loop.pre_loop < len(string.ascii_uppercase) else f"Z{current_loop.pre_loop - 25}"
        question = (
            prompt_template_establishment_cross
            .replace("<The code I give you>", prompt_code)
            .replace("<ERROR_MSG_HERE>", error_msg)     
            .replace("<CUR_LOOP>", current_loop.alphabet)
            .replace("<PRE_LOOP>", pre_loop_alphabet)
            .replace("<PRE_STATE>", current_loop.pre_state)
        )
    elif prompt_type == "preservation_nested":
        inner_loop_alphabet = (
            string.ascii_uppercase[inner_loop.index]
            if inner_loop.index < len(string.ascii_uppercase)
            else f"Z{inner_loop.index - 25}"
        )
        question = (
            prompt_template_preservation_nested
            .replace("<The code I give you>", prompt_code)
            .replace("<ERROR_MSG_HERE>", error_msg)
            .replace("<CUR_LOOP>", current_loop.alphabet)
            .replace("<INNER_LOOP>", inner_loop_alphabet)
            .replace("<INNER_POST_STATE>", inner_loop.post_state)
        )
    elif prompt_type == "preservation_self":   
        loop_body_text = current_loop.loop_state
        question = (
            prompt_template_preservation_self
            .replace("<The code I give you>", prompt_code)
            .replace("<LOOP_ALPHABET>", current_loop.alphabet)
            .replace("<LOOP_BODY>", loop_body_text)
            .replace("<ERROR_MSG_HERE>", error_msg)
        )
    else:
        question = ""
    return question


if __name__ == "__main__":
    with open("../Benchmark/acsl-algorithms/_edit_distance.c", "r", encoding="utf-8") as f:
        c = f.read()
    print(get_prompt(c, 'establishment_cross'))