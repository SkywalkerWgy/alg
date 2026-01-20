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
        loop invariant i_0: 0 <= i < n;

        loop invariant i_1: 0 <= j < n;

        loop invariant i_2: 0 <= k < n;

        loop invariant i_3: k >= 2*i;

        loop invariant i_4: j == 2*i;

        loop invariant i_5: i < n && k >= j;

        loop invariant i_6: n <= INT_MAX;

        loop invariant i_7: k <= n;

        loop invariant i_8: j <= n;

        loop invariant i_26: k >= 2 * i;

        loop invariant i_27: j == 2 * i;

        loop invariant i_28: 0 <= i < n && n <= INT_MAX;

        loop invariant i_29: 0 <= j < n && j <= n;

        loop invariant i_30: 0 <= k < n && k <= n;

        loop invariant i_31: 0 <= i < n && 0 <= j < n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_17: 0 <= i < n;

            loop invariant i_18: 0 <= j < n;

            loop invariant i_19: 0 <= k < n;

            loop invariant i_20: k >= 2*i;

            loop invariant i_21: j == 2*i;

            loop invariant i_22: i < n && k >= j;

            loop invariant i_23: n <= INT_MAX;

            loop invariant i_24: k <= n;

            loop invariant i_25: j <= n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_9: 0 <= i < n;

                    loop invariant i_10: 0 <= j < n;

                    loop invariant i_11: 0 <= k < n;

                    loop invariant i_12: k >= 2*i;

                    loop invariant i_13: j == 2*i;

                    loop invariant i_14: i < n && k >= j;

                    loop invariant i_15: n <= INT_MAX;

                    loop invariant i_16: k <= n;


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