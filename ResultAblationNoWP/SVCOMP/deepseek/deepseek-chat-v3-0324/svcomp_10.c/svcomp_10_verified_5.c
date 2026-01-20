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
        loop invariant i_21: i <= n + 1;

        loop invariant i_22: k == n - (i / 2);

        loop invariant i_23: (i % 2) == 0;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_24: j <= n / 2;

        loop invariant i_25: k == n - (n / 2) - j;

        loop invariant i_26: k > 0;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}