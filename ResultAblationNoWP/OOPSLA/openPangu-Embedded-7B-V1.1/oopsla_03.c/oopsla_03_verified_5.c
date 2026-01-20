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
        loop invariant i_77: 1 <= n;

        loop invariant i_78: 1 <= l;

        loop invariant i_79: k >= 1;

        loop invariant i_80: k < n;

        loop invariant i_81: i >= l;

        loop invariant i_82: i < n;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_92: 1 <= i;

            loop invariant i_93: l <= i;

            loop invariant i_94: 1 <= n;

            loop invariant i_95: 1 <= l;

            loop invariant i_96: k >= 1;

            loop invariant i_97: i >= l;

            loop invariant i_98: k < n;

            loop invariant i_99: i < n;

            loop invariant i_100: k >= 1 && i == k;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_83: 1 <= i;

            loop invariant i_84: l <= i;

            loop invariant i_85: 1 <= n;

            loop invariant i_86: 1 <= l;

            loop invariant i_87: k >= 1;

            loop invariant i_88: k < n;

            loop invariant i_89: i >= l;

            loop invariant i_90: i < n;

            loop invariant i_91: k >= 1 && i == k;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
