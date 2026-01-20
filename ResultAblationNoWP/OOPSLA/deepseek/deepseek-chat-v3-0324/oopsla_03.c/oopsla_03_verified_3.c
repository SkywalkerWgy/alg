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
        loop invariant i_18: 1 <= k <= n;

        loop invariant i_19: \forall integer j; 1 <= j < k ==> \exists integer m; l <= m < n;

        loop invariant i_20: k > 1 ==> \forall integer m; l <= m < n;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_24: s for Loop B: ``` loop invariant l <= i <= n;

            loop invariant i_25: l <= i <= n;

            loop invariant i_26: \forall integer m; l <= m < i ==> m < n;

            loop invariant i_27: i == l || i > l;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_21: l <= i <= n;

            loop invariant i_22: \forall integer m; l <= m < i ==> m < n;

            loop invariant i_23: i == l || i > l;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
