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

        loop invariant i_1: \forall integer p; 0 <= p < i ==> (\forall integer q; 2*p <= q < n ==> (unknown1() ==> (\forall integer r; q <= r < n ==> r >= 2*p)) && (!unknown1() ==> (k >= n && k <= n))); loop invariant k == n; ```;

        loop invariant i_2: k == n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_5: 2*i <= j <= n;

            loop invariant i_6: k == n;

            loop invariant i_7: \forall integer p; 0 <= p < i ==> (\forall integer q; 2*p <= q < n ==> (unknown1() ==> (\forall integer r; q <= r < n ==> r >= 2*p)) && (!unknown1() ==> (k >= n && k <= n))); ```;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_3: j <= k <= n;

                    loop invariant i_4: \forall integer r; j <= r < k ==> r >= 2*i;


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