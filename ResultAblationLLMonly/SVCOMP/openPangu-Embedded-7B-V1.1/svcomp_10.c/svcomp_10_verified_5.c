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
        loop invariant i_20: k >= 0 && i <= n && (n - k) == i;

        loop invariant i_21: j >= 0 && k >= j;

        loop invariant i_22: ...;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_23: k >= 0 && i <= n && (n - k) == i;

        loop invariant i_24: j >= 0 && k >= j && k > 0 && j <= n/2;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}