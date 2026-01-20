/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_19: && 0 <= i < n;

        loop invariant i_20: && 0 <= k < n;

        loop invariant i_21: && i + k == n;

        loop invariant i_22: && k > 0 || j == n;

        loop invariant i_23: && j + k == n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_24: && 0 <= i < n;

        loop invariant i_25: && k > 0 && j == n;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}