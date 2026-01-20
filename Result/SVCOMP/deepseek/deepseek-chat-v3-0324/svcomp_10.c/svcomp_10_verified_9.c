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
        loop invariant i_1: k == n - i/2;

        loop invariant i_2: (i % 2) == 0;

        loop invariant i_6: 0 <= i;

        loop invariant i_7: n - k >= 0;

        loop invariant i_8: i == 2*(n - k);


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_3: 0 <= j <= n/2;

        loop invariant i_4: k == n - i/2 - j;

        loop invariant i_5: i == 2*(n - k - j);

        loop invariant i_9: k == n - (i/2) - j;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}