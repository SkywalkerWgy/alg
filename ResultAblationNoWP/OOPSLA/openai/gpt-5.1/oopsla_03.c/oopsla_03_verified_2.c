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
        loop invariant i_0: 1 <= k;

        loop invariant i_1: k <= n;

        loop invariant i_2: l > 0;

        loop invariant i_3: n > l;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_10: 1 <= k;

            loop invariant i_11: k <= n;

            loop invariant i_12: l > 0;

            loop invariant i_13: n > l;

            loop invariant i_14: l <= i <= n;

            loop invariant i_15: 1 <= i;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_4: 1 <= k;

            loop invariant i_5: k <= n;

            loop invariant i_6: l > 0;

            loop invariant i_7: n > l;

            loop invariant i_8: l <= i <= n;

            loop invariant i_9: 1 <= i;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
