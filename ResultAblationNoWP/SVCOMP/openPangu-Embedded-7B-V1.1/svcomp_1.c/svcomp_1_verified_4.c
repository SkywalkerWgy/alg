int svcomp_1() {
    int x = 1;
    int y = 0;
    // Loop A
    /*@
        loop invariant i_16: && y < 1000;

        loop invariant i_17: is inferred purely based on the program logic and standard correctness requirements for loop invariants. The loop invariant is `y < 1000`, which must hold true before and after each iteration of the loop. The variable `x` is updated using `y`, but since `y` is incremented in each iteration, `y < 1000` is the invariant that constrains the loop's termination condition. The invariant `x >= y` is not guaranteed at the end of the loop (since the loop exits when `y == 1000`, and `x` may be `y + sum of all previous y values`), so it cannot be part of the loop invariant. If pre- or post-conditions were provided (e.g., `requires` or `assert` clauses), the invariant would be adjusted accordingly. Since they are not present in the code snippet, only the standard loop invariant is provided. **Note:** The loop invariant is placed in ACSL as follows: ```acsl loop invariant && y < 1000;

        loop invariant i_18: s. The loop invariant is `y < 1000`, which must hold true before and after each iteration of the loop. The variable `x` is updated using `y`, but since `y` is incremented in each iteration, `y < 1000` is the invariant that constrains the loop's termination condition. The invariant `x >= y` is not guaranteed at the end of the loop (since the loop exits when `y == 1000`, and `x` may be `y + sum of all previous y values`), so it cannot be part of the loop invariant. If pre- or post-conditions were provided (e.g., `requires` or `assert` clauses), the invariant would be adjusted accordingly. Since they are not present in the code snippet, only the standard loop invariant is provided. **Note:** The loop invariant is placed in ACSL as follows: ```acsl loop invariant && y < 1000;

        loop invariant i_19: is `y < 1000`, which must hold true before and after each iteration of the loop. The variable `x` is updated using `y`, but since `y` is incremented in each iteration, `y < 1000` is the invariant that constrains the loop's termination condition. The invariant `x >= y` is not guaranteed at the end of the loop (since the loop exits when `y == 1000`, and `x` may be `y + sum of all previous y values`), so it cannot be part of the loop invariant. If pre- or post-conditions were provided (e.g., `requires` or `assert` clauses), the invariant would be adjusted accordingly. Since they are not present in the code snippet, only the standard loop invariant is provided. **Note:** The loop invariant is placed in ACSL as follows: ```acsl loop invariant && y < 1000;

        loop invariant i_20: . If pre- or post-conditions were provided (e.g., `requires` or `assert` clauses), the invariant would be adjusted accordingly. Since they are not present in the code snippet, only the standard loop invariant is provided. **Note:** The loop invariant is placed in ACSL as follows: ```acsl loop invariant && y < 1000;

        loop invariant i_21: is provided. **Note:** The loop invariant is placed in ACSL as follows: ```acsl loop invariant && y < 1000;

        loop invariant i_22: is placed in ACSL as follows: ```acsl loop invariant && y < 1000;


        loop assigns y;
        loop assigns x;
    */
    while (y < 1000 ) {
        x = x + y;
        y = y + 1;
    }
    //@ assert x >= y;
    return 0;
}