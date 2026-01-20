// jm2006_variant_true-unreach-call.c

/*@
    requires 0 <= i && i < 1000000;
    requires j >= 0;
*/
int svcomp_13(int i, int j) {
    int x = i;
    int y = j;
    int z = 0;

    // Loop A
    /*@
        loop invariant i_4: x >= 0 && x <= j;

        loop invariant i_5: y >= -z && y <= j - z;

        loop invariant i_6: in the provided code does not include the `i` constraint `0 <= i && i < 1000000`, as the loop only runs when `x != 0`, which depends on the initial value of `x = i`. Since `x` is modified inside the loop, the loop invariant does not need to preserve the original `i` value beyond its initial assignment. The loop condition `x != 0` is equivalent to `x >= 1`, which is consistent with `i >= 1`. However, since the original `requires` clause includes `i` in the precondition, if you want to ensure the invariant holds even if the loop is entered after the precondition is satisfied, you may consider adding: loop invariant 0 <= i && i < 1000000;

        loop invariant i_7: does not need to preserve the original `i` value beyond its initial assignment. The loop condition `x != 0` is equivalent to `x >= 1`, which is consistent with `i >= 1`. However, since the original `requires` clause includes `i` in the precondition, if you want to ensure the invariant holds even if the loop is entered after the precondition is satisfied, you may consider adding: loop invariant 0 <= i && i < 1000000;

        loop invariant i_8: 0 <= i && i < 1000000;


        loop assigns x, y, z;
    */
    while (x != 0) {
    	x--;
    	y -= 2;
    	z++;
    }

    if (i == j) {
    	//@ assert(y == -z);
    }
    
    return 0;
}
