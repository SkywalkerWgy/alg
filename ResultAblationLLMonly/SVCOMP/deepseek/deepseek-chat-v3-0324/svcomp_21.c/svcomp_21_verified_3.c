/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_0: k == i;

        loop invariant i_1: 0 <= i <= n;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_2: k == j + (i - j);

        loop invariant i_3: 0 <= j <= n;

        loop invariant i_4: k == i - j;

        loop invariant i_5: k + j == i;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}