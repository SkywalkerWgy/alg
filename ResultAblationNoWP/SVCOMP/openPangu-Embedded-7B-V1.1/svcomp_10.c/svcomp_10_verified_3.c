# define INT_MAX 2147483647

/*@
    requires n <= INT_MAX;
*/
int svcomp_10(int n) {
    int i,k;
    k = n;
    i = 0;

    // Loop A
    /*@
        loop invariant i_11: k >= n && i == 0;

        loop invariant i_12: i < n;

        loop invariant i_13: k >= j;

        loop invariant i_14: j < n / 2;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_15: k >= n && i == 0 && k >= j && i < n && j < n / 2;

        loop invariant i_16: k >= j && j < n / 2 && k > 0 && i == 0;

        loop invariant i_17: j >= 0 && j < n / 2 && k >= 0;

        loop invariant i_18: k >= n && i == 0 && j == 0 && k >= j && i < n && j < n / 2;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}