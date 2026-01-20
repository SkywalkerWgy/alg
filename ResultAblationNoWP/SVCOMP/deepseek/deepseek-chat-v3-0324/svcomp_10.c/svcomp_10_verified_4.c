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
        loop invariant i_15: i >= 0 && i <= n;

        loop invariant i_16: k == n - (i / 2);

        loop invariant i_17: (i % 2) == 0;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_18: j >= 0 && j <= n/2;

        loop invariant i_19: k == n - (n + j);

        loop invariant i_20: k > 0;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}