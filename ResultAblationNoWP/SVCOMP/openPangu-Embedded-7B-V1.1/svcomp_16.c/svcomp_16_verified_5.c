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
        loop invariant i_77: i < n;

        loop invariant i_78: j >= 2 * i;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_81: i < n;

            loop invariant i_82: j >= 2 * i;

            loop invariant i_83: k >= n || k == j;

            loop invariant i_84: k <= n || k == j;

            loop invariant i_85: \exists integer p; 0 <= p < i && svcomp_16(k, p);


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_79: i < n;

                    loop invariant i_80: j >= 2 * i;


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