/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_15: i + k == n && i < n;

        loop invariant i_16: j == n - i && j >= 0;

        loop invariant i_17: k >= 0 && k < n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_18: 1 < n;

        loop invariant i_19: j >= 0 && j < n && k >= 0 && k < n;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}