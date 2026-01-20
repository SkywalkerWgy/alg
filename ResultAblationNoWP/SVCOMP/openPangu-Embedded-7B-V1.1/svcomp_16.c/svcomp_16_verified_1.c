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
        loop invariant i_0: k >= 2*i && k < n;

        loop invariant i_1: 0 <= i < n;

        loop invariant i_2: j >= 2*i && j < n;

        loop invariant i_3: 0 <= j < n && j == 2*i;

        loop invariant i_4: 0 <= k < n && k == j;

        loop invariant i_5: n >= i && n >= j;

        loop invariant i_6: n >= 2*i;

        loop invariant i_7: n >= n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_16: k >= 2*i && k < n;

            loop invariant i_17: 0 <= i < n;

            loop invariant i_18: j >= 2*i && j < n;

            loop invariant i_19: 0 <= j < n && j == 2*i;

            loop invariant i_20: 0 <= k < n && k == j;

            loop invariant i_21: n >= i && n >= j;

            loop invariant i_22: n >= 2*i;

            loop invariant i_23: n >= n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_8: k >= 2*i && k < n;

                    loop invariant i_9: 0 <= i < n;

                    loop invariant i_10: j >= 2*i && j < n;

                    loop invariant i_11: 0 <= j < n && j == 2*i;

                    loop invariant i_12: 0 <= k < n && k == j;

                    loop invariant i_13: n >= i && n >= j;

                    loop invariant i_14: n >= 2*i;

                    loop invariant i_15: n >= n;


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