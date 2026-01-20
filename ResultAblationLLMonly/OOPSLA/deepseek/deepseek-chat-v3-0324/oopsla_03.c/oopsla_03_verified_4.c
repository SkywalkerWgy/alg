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
        loop invariant i_0: s for Loop A: ``` loop invariant 1 <= k <= n;

        loop invariant i_1: 1 <= k <= n;

        loop invariant i_2: \forall integer j; l <= j < n ==> j >= l;

        loop invariant i_3: \forall integer j; l <= j < n ==> j < n;

        loop invariant i_8: \forall integer j; l <= j < n ==> j >= l && j < n;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_4: l <= i <= n;

            loop invariant i_5: \forall integer j; l <= j < i ==> j < n;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_6: l <= i <= n;

            loop invariant i_7: \forall integer j; l <= j < i ==> j < n;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
