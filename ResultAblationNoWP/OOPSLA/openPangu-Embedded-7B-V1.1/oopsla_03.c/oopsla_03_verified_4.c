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
        loop invariant i_66: k >= 1;

        loop invariant i_67: i >= l;

        loop invariant i_68: i < n;

        loop invariant i_69: for the following loop. loop assigns k;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_73: k >= 1;

            loop invariant i_74: i >= l;

            loop invariant i_75: i < n;

            loop invariant i_76: 1 <= i;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_70: i >= l;

            loop invariant i_71: i < n;

            loop invariant i_72: 1 <= i;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
