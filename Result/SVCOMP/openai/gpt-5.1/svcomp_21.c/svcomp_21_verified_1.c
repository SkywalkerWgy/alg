/*@
    requires n > 0;
*/
void svcomp_21(int n) {
    int i = 0;
    int k = 0;
    
    // Loop A
    /*@
        loop invariant i_0: n > 0;

        loop invariant i_1: 0 <= i <= n;

        loop invariant i_2: k == i;


        loop assigns i, k;
    */
    while( i < n ) {
        i++;
        k++;
    }

    int j = 0;

    // Loop B
    /*@
        loop invariant i_3: n > 0;

        loop invariant i_4: 0 <= j && j <= n;

        loop invariant i_5: 0 <= k && k <= n;

        loop invariant i_6: j + k == n;


        loop assigns j, k;
    */
    while( j < n ) {
        //@ assert (k > 0);
        j++;
        k--;
    }
}