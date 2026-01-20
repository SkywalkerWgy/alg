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
        loop invariant i_0: s for Loop A: ``` loop invariant 0 <= i <= n;

        loop invariant i_1: 0 <= i <= n;

        loop invariant i_2: k == n;

        loop invariant i_3: \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (unknown1() ==> (\forall integer q; p <= q < n ==> q >= 2*m))); loop invariant \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (!unknown1() ==> (k >= n && k <= n))); ```;

        loop invariant i_4: \forall integer m; 0 <= m < i ==> (\forall integer p; 2*m <= p < n ==> (!unknown1() ==> (k >= n && k <= n))); ```;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_5: s for Loop B: ``` loop invariant 2*i <= j <= n;

            loop invariant i_6: 2*i <= j <= n;

            loop invariant i_7: \forall integer p; 2*i <= p < j ==> (unknown1() ==> (\forall integer q; p <= q < n ==> q >= 2*i)); loop invariant \forall integer p; 2*i <= p < j ==> (!unknown1() ==> (k >= n && k <= n));

            loop invariant i_8: \forall integer p; 2*i <= p < j ==> (!unknown1() ==> (k >= n && k <= n));


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_9: j <= k <= n;

                    loop invariant i_10: \forall integer q; j <= q < k ==> q >= 2*i;


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