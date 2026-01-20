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
        loop invariant i_5: i >= 0 && i <= n + 1;

        loop invariant i_6: k == n - (i / 2);


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_7: j >= 0 && j <= n/2;

        loop invariant i_8: k == n - (i/2) - j;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}