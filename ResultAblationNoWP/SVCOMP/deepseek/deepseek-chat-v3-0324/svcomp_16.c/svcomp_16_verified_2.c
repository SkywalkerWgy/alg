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
        loop invariant i_8: 0 <= i <= n;

        loop invariant i_9: \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (unknown1() ==> (\forall integer q; p <= q < n ==> q >= 2*m))); loop invariant \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (!unknown1() ==> (k >= n && k <= n))); loop invariant k == n; ```;

        loop invariant i_10: \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (!unknown1() ==> (k >= n && k <= n))); loop invariant k == n;

        loop invariant i_11: k == n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_15: 2*i <= j <= n;

            loop invariant i_16: k == n;

            loop invariant i_17: \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (unknown1() ==> (\forall integer q; p <= q < n ==> q >= 2*m))); loop invariant \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (!unknown1() ==> (k >= n && k <= n))); ```;

            loop invariant i_18: \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (!unknown1() ==> (k >= n && k <= n))); ```;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_12: j <= k <= n;

                    loop invariant i_13: \forall integer q; j <= q < k ==> q >= 2*i;

                    loop invariant i_14: k == n ==> \forall integer q; j <= q < n ==> q >= 2*i;


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