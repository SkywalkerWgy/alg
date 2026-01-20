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
        loop invariant i_28: s for Loop A: ``` loop invariant 1 <= k <= n;

        loop invariant i_29: 1 <= k <= n;

        loop invariant i_30: \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m >= 1); loop invariant \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m < n); ```;

        loop invariant i_31: \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m < n); ```;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_36: l <= i <= n;

            loop invariant i_37: \forall integer m; l <= m < i ==> m >= l && m < n;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_32: s for Loop C: ``` loop invariant l <= i <= n;

            loop invariant i_33: l <= i <= n;

            loop invariant i_34: \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m >= 1); loop invariant \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m < n); ```;

            loop invariant i_35: \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m < n); ```;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
