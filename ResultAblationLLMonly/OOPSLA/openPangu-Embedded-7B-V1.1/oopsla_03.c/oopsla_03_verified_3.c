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
        loop invariant i_21: 1 <= k;

        loop invariant i_22: 1 <= k && k < n;

        loop invariant i_23: 1 <= i && i >= l;

        loop invariant i_24: 1 <= i && i < n;

        loop invariant i_25: 1 <= i && i >= l && 1 <= i < n;

        loop invariant i_26: 1 <= k && k < n && 1 <= i && i < n;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_33: 1 <= k;

            loop invariant i_34: 1 <= k && k < n;

            loop invariant i_35: 1 <= i && i >= l;

            loop invariant i_36: 1 <= i && i < n;

            loop invariant i_37: 1 <= k && k < n && 1 <= i && i < n;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_27: 1 <= k;

            loop invariant i_28: 1 <= k && k < n;

            loop invariant i_29: 1 <= i && i >= l;

            loop invariant i_30: 1 <= i && i < n;

            loop invariant i_31: 1 <= i && i >= l && 1 <= i < n;

            loop invariant i_32: 1 <= k && k < n && 1 <= i && i < n;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
