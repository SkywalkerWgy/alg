/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_16: i + k == n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_17: i + k == n;

        loop invariant i_18: j + k == k;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}