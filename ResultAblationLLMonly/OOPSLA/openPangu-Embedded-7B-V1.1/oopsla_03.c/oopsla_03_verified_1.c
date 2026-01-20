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
        loop invariant i_0: 1 <= k && 1 <= n;

        loop invariant i_1: l <= i;

        loop invariant i_2: l <= i && 1 <= i;

        loop invariant i_3: l <= i && 1 <= i && 1 <= k && 1 <= n;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_5: 1 <= i && l <= i && 1 <= n;

            loop invariant i_6: 1 <= i && l <= i && 1 <= k && 1 <= n;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_4: 1 <= i && l <= i && 1 <= k && 1 <= n;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
