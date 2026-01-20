/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    /*@
        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    /*@
        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}