/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_10: i + k == n && i < n;

        loop invariant i_11: j == n - i && j < n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_12: i + k == n && i < n;

        loop invariant i_13: j == n - i && j < n;

        loop invariant i_14: k >= 0 && k < n;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}