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
        loop invariant i_0: 1 <= k <= n;

        loop invariant i_1: \forall integer j; 1 <= j < k ==> (\forall integer m; l <= m < n ==> m >= 1); ```;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_5: l <= i <= n;

            loop invariant i_6: \forall integer m; l <= m < i ==> m >= 1;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_2: s for Loop C: ``` loop invariant l <= i <= n;

            loop invariant i_3: l <= i <= n;

            loop invariant i_4: \forall integer m; l <= m < i ==> m >= 1;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
