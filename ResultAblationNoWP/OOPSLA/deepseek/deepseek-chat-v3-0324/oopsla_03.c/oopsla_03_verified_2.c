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
        loop invariant i_7: s for Loop A: ``` loop invariant 1 <= k <= n;

        loop invariant i_8: 1 <= k <= n;

        loop invariant i_9: \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m >= 1); loop invariant l > 0 && n > l;

        loop invariant i_10: l > 0 && n > l;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_14: s for Loop B: ``` loop invariant l <= i <= n;

            loop invariant i_15: l <= i <= n;

            loop invariant i_16: \forall integer m; l <= m < i ==> m >= 1;

            loop invariant i_17: l > 0 && n > l;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_11: l <= i <= n;

            loop invariant i_12: \forall integer m; l <= m < i ==> m >= 1;

            loop invariant i_13: l > 0 && n > l;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
