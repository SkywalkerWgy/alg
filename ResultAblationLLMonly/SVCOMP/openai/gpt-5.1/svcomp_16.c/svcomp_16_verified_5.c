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
        loop invariant i_0: 0 <= i <= n;

        loop invariant i_1: k == n;

        loop invariant i_2: n < INT_MAX;

        loop invariant i_15: 0 <= i && i <= n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_3: 0 <= i <= n;

            loop invariant i_4: j >= 2 * i;

            loop invariant i_5: k >= n;

            loop invariant i_6: k <= n;

            loop invariant i_7: n < INT_MAX;

            loop invariant i_16: 0 <= i && i <= n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_8: 0 <= i <= n;

                    loop invariant i_9: j >= 2 * i;

                    loop invariant i_10: j < n;

                    loop invariant i_11: k >= j;

                    loop invariant i_12: k >= 2 * i;

                    loop invariant i_13: k <= n;

                    loop invariant i_14: n < INT_MAX;

                    loop invariant i_17: 2 * i <= j;

                    loop invariant i_18: j <= k;

                    loop invariant i_19: 2 * i <= k;


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