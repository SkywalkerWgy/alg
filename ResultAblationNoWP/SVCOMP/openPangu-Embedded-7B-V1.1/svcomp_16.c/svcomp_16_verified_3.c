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
        loop invariant i_43: k >= 2*i && k < n;

        loop invariant i_44: i < n;

        loop invariant i_45: j >= 2*i && j < n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_50: i < n;

            loop invariant i_51: k >= 2*i && k < n;

            loop invariant i_52: j >= 2*i && j < n;

            loop invariant i_53: \forall integer k; 0 <= k < i ==> max(unknown1()) == n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_46: i < n;

                    loop invariant i_47: k >= 2*i && k < n;

                    loop invariant i_48: j >= 2*i && j < n;

                    loop invariant i_49: \forall integer k; 0 <= k < i ==> max(unknown1()) == n;


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