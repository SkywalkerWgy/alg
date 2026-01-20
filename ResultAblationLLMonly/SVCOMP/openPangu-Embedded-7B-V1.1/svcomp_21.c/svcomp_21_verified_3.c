/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_7: 0 <= i < n;

        loop invariant i_8: 0 <= k < n;

        loop invariant i_9: i + k == n;

        loop invariant i_10: j >= 0;

        loop invariant i_11: k >= 0;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_12: 0 <= i < n;

        loop invariant i_13: 0 <= k < n;

        loop invariant i_14: i + k == n;

        loop invariant i_15: k >= 0;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}