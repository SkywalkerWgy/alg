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
        loop invariant i_34: i < n;

        loop invariant i_35: j >= 2*i;

        loop invariant i_36: k >= j;

        loop invariant i_37: j < n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_44: i < n;

            loop invariant i_45: j >= 2*i;

            loop invariant i_46: k >= j;

            loop invariant i_47: j < n;

            loop invariant i_48: k <= n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_38: j >= 2*i;

                    loop invariant i_39: k >= 2*i;

                    loop invariant i_40: i < n;

                    loop invariant i_41: j < n;

                    loop invariant i_42: k >= j;

                    loop invariant i_43: k <= n;


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