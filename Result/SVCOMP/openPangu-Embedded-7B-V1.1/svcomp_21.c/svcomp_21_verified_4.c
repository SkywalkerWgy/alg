/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_0: i + k == n && i < n;

        loop invariant i_7: i < n;

        loop invariant i_8: k < n;

        loop invariant i_9: i + k == n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_2: i + k == n && i < n;

        loop invariant i_3: j == n - i - k && j >= 0;

        loop invariant i_4: k > 0;

        loop invariant i_5: j >= 0 && j < n;

        loop invariant i_6: k >= 0 && k < n;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}