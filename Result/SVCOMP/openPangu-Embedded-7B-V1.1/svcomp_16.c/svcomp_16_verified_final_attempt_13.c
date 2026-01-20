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
        loop invariant i_6: n <= INT_MAX;

        loop invariant i_7: k <= n;

        loop invariant i_29: 0 <= j < n && j <= n;

        loop invariant i_31: 0 <= i < n && 0 <= j < n;

        loop invariant i_33: 0 <= i < n;

        loop invariant i_34: 0 <= j < n;

        loop invariant i_35: 0 <= k < n;

        loop invariant i_36: k >= i;

        loop invariant i_37: j >= i;

        loop invariant i_38: i < n;

        loop invariant i_39: k >= j;


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