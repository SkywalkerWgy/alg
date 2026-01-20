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
        loop invariant i_15: 0 <= i && i < 1000000;

        loop invariant i_16: j >= 0;

        loop invariant i_17: x == i - j;

        loop invariant i_18: z == i - j + 1;

        loop invariant i_19: x <= y && y - z == i;

        loop invariant i_20: y >= z;

        loop invariant i_21: z <= i;


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
