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
        loop invariant i_7: k == 1;

        loop invariant i_8: 1 <= k && k < n;

        loop invariant i_9: 1 <= i && i < n;

        loop invariant i_10: i == l;

        loop invariant i_11: 1 <= i && i < n ==> max >= a[i];


        loop assigns k;
        loop assigns i;
    */
    for (k=1; k<n; k++){
        
        // Loop B
        /*@
            loop invariant i_16: 1 <= i && i < n;

            loop invariant i_17: 1 <= k && k < n;

            loop invariant i_18: i == l;

            loop invariant i_19: 1 <= i && i < n ==> max >= a[i];

            loop invariant i_20: 1 <= k && k < n ==> max >= a[i];


            loop assigns i;
        */
        for (i=l; i<n; i++) {
        }
        
        // Loop C
        /*@
            loop invariant i_12: 1 <= i && i < n;

            loop invariant i_13: 1 <= k && k < n;

            loop invariant i_14: i == l;

            loop invariant i_15: 1 <= k && k < n ==> max >= a[i];


            loop assigns k;
            loop assigns i;
        */
        for (i=l; i<n; i++) {
            //@ assert a_1: 1<=i;
        }
    }

}
