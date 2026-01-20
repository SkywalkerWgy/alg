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
        loop invariant i_24: k >= 2*i && k < n;

        loop invariant i_25: i < n;

        loop invariant i_26: ...;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_35: k >= 2*i && k < n;

            loop invariant i_36: i < n;

            loop invariant i_37: k <= n;

            loop invariant i_38: j >= 2*i && j < n;

            loop invariant i_39: j < n;

            loop invariant i_40: k >= 2*i;

            loop invariant i_41: j >= 2*i;

            loop invariant i_42: k;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_27: k >= 2*i && k < n;

                    loop invariant i_28: i < n;

                    loop invariant i_29: k <= n;

                    loop invariant i_30: j >= 2*i && j < n;

                    loop invariant i_31: j < n;

                    loop invariant i_32: k >= 2*i;

                    loop invariant i_33: j >= 2*i;

                    loop invariant i_34: k;


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