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
        loop invariant i_9: i <= n + 1;

        loop invariant i_10: k == n - (i / 2);

        loop invariant i_11: (i % 2) == 0;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_12: 0 <= j <= n/2;

        loop invariant i_13: k == n - (i/2) - j;

        loop invariant i_14: k > 0;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}