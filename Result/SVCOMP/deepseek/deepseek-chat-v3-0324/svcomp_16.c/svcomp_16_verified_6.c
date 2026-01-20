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

        loop invariant i_2: \forall integer m; 0 <= m < i ==> \forall integer p; 2*m <= p < n ==> (k >= p || k >= n);

        loop invariant i_8: 0 <= i;

        loop invariant i_9: 2*i <= n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_3: 2*i <= j <= n;

            loop invariant i_4: k == n;

            loop invariant i_5: \forall integer m; 0 <= m < j ==> (k >= m || k >= n);

            loop invariant i_13: \forall integer m; 0 <= m < i ==> \forall integer p; 2*m <= p < n ==> (k >= p || k >= n);


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_6: j <= k <= n;

                    loop invariant i_7: k == n || \forall integer p; j <= p < k ==> p >= 2*i;

                    loop invariant i_10: k >= 2*i;

                    loop invariant i_11: \forall integer p; j <= p < k ==> p >= 2*i;

                    loop invariant i_12: \forall integer m; 0 <= m < i ==> \forall integer p; 2*m <= p < n ==> (k >= p || k >= n);

                    loop invariant i_14: 2*i <= n;


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