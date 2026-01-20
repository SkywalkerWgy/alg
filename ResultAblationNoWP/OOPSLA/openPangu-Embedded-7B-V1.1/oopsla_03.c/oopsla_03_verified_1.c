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
        loop invariant i_0: k >= 1;

        loop invariant i_1: k < n;

        loop invariant i_2: i >= l;

        loop invariant i_3: 1 <= i;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_8: k >= 1;

            loop invariant i_9: k < n;

            loop invariant i_10: i >= l;

            loop invariant i_11: 1 <= i;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_4: k >= 1;

            loop invariant i_5: k < n;

            loop invariant i_6: i >= l;

            loop invariant i_7: 1 <= i;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
