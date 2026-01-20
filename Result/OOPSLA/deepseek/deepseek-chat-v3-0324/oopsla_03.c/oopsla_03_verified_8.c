/*
 * "nested4.c" from InvGen benchmark suite
 */

/*@
    requires l > 0;
    requires n > l;
*/
void oopsla_03(int n, int l) {
    int i,k;

    // Loop A
    /*@
        loop invariant i_1: 1 <= k <= n;

        loop invariant i_2: \forall integer j; l <= j < n ==> j >= l;

        loop invariant i_13: 1 <= k < n;

        loop invariant i_15: n > l;

        loop invariant i_18: k >= 1;

        loop invariant i_19: k < n;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_4: l <= i <= n;

            loop invariant i_5: \forall integer j; l <= j < i ==> j >= l;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_8: l <= i <= n;

            loop invariant i_10: \forall integer j; l <= j < i ==> j >= l;

            loop invariant i_11: 1 <= k <= n;

            loop invariant i_12: 1 <= k < n;

            loop invariant i_16: k <= n;

            loop invariant i_17: k >= 1;

            loop invariant i_20: k+1 <= n;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
