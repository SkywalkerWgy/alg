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
        loop invariant i_0: 0 <= i && i < 1000000;

        loop invariant i_1: j >= 0;

        loop invariant i_2: x >= 0;

        loop invariant i_3: z >= 0;

        loop invariant i_4: x + z == i;

        loop invariant i_5: y + 2*z == j;


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
