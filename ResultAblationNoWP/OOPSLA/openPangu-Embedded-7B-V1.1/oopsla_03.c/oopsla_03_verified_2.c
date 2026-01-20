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
        loop invariant i_12: 1 <= n;

        loop invariant i_13: 1 <= l;

        loop invariant i_14: k < n;

        loop invariant i_15: 1 <= i;

        loop invariant i_16: i < n;

        loop invariant i_17: k == i;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_24: 1 <= n;

            loop invariant i_25: 1 <= l;

            loop invariant i_26: k < n;

            loop invariant i_27: 1 <= i;

            loop invariant i_28: i < n;

            loop invariant i_29: k == i;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_18: 1 <= n;

            loop invariant i_19: 1 <= l;

            loop invariant i_20: k < n;

            loop invariant i_21: 1 <= i;

            loop invariant i_22: i < n;

            loop invariant i_23: k == i;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
