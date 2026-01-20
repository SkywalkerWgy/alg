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
        loop invariant i_0: k == 1;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_8: 1 <= k;

            loop invariant i_9: i >= l;

            loop invariant i_12: k == 1;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_4: k == 1;

            loop invariant i_5: i >= l;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
