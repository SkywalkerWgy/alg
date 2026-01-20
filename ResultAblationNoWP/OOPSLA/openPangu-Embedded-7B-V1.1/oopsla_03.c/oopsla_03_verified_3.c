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
        loop invariant i_30: k >= 1;

        loop invariant i_31: k < n;

        loop invariant i_32: k == i;

        loop invariant i_33: i >= l;

        loop invariant i_34: i < n;

        loop invariant i_35: i == k;

        loop invariant i_36: l == 0 && k == 1;

        loop invariant i_37: 1 <= i;

        loop invariant i_38: i == l;

        loop invariant i_39: l > 0 && i == l;

        loop invariant i_40: 1 <= i && l > 0 && i == l;

        loop invariant i_41: l == 0;

        loop invariant i_42: i == l && 1 <= i;


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_55: k >= 1 && k < n;

            loop invariant i_56: k == i;

            loop invariant i_57: i >= l;

            loop invariant i_58: i < n;

            loop invariant i_59: i == k;

            loop invariant i_60: l == 0 && k == 1;

            loop invariant i_61: 1 <= i;

            loop invariant i_62: i == l;

            loop invariant i_63: l > 0 && i == l;

            loop invariant i_64: l == 0;

            loop invariant i_65: i == l && 1 <= i;


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_43: k >= 1;

            loop invariant i_44: k < n;

            loop invariant i_45: k == i;

            loop invariant i_46: i >= l;

            loop invariant i_47: i < n;

            loop invariant i_48: i == k;

            loop invariant i_49: l == 0 && k == 1;

            loop invariant i_50: 1 <= i;

            loop invariant i_51: i == l;

            loop invariant i_52: l > 0 && i == l;

            loop invariant i_53: l == 0;

            loop invariant i_54: i == l && 1 <= i;


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
