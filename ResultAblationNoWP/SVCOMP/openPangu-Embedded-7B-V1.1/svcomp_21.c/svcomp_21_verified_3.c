/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_6: i >= 0 && i < n;

        loop invariant i_7: k >= 0 && k < n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_8: i >= 0 && i < n && k >= 0 && k < n;

        loop invariant i_9: j >= 0 && j < n && k >= 0 && k > 0;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}