# define INT_MAX 2147483647

int unknown1();

/*@
    requires n < INT_MAX;
*/
int svcomp_16(int k, int n) {
    int i, j;

    if(k == n) {
    }
    else {
        goto END;
    }
    // Loop A
    /*@
        loop invariant i_13: i < n;

        loop invariant i_14: j >= 2 * i;

        loop invariant i_15: k >= j;

        loop invariant i_16: k <= n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_22: i < n;

            loop invariant i_23: j >= 2 * i;

            loop invariant i_24: k >= j;

            loop invariant i_25: k <= n;

            loop invariant i_26: k >= n;

            loop invariant i_27: k >= 2 * i;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_17: k >= 2 * i;

                    loop invariant i_18: j >= 2 * i;

                    loop invariant i_19: k <= n;

                    loop invariant i_20: i < n;

                    loop invariant i_21: k >= j;


                    loop assigns k;
                */
                for (k = j; k < n; k++) {
                    //@ assert(k >= 2*i);
                }
            }
            else {
                //@ assert( k >= n );
                //@ assert( k <= n );
            }
        }
    }

END:
    return 0;
}