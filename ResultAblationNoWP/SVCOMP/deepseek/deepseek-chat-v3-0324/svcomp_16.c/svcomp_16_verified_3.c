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
        loop invariant i_19: 0 <= i <= n;

        loop invariant i_20: \forall integer p; 0 <= p < i ==> \forall integer q; 2*p <= q < n ==> (k >= q || k >= n);

        loop invariant i_21: k >= n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_24: 2*i <= j <= n;

            loop invariant i_25: \forall integer q; 2*i <= q < j ==> (k >= q || k >= n);

            loop invariant i_26: k >= n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_22: j <= k <= n;

                    loop invariant i_23: \forall integer m; j <= m < k ==> m >= 2*i;


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