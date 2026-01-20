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
        loop invariant i_9: x >= 0 && x <= i;

        loop invariant i_10: y >= -i - 1 && y <= j - 2*i;

        loop invariant i_11: z <= i;


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
