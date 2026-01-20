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
        loop invariant i_0: n <= INT_MAX;

        loop invariant i_1: 0 <= i;

        loop invariant i_2: i % 2 == 0;

        loop invariant i_3: k + i/2 == n;

        loop invariant i_4: n >= 0 ==> i <= n + 1;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_5: n <= INT_MAX;

        loop invariant i_6: 0 <= j;

        loop invariant i_7: (n >= 0 ==> k == n/2 - j);

        loop invariant i_8: (n <= 0 ==> k == n - j);

        loop invariant i_9: j >= 0;

        loop invariant i_10: n >= 0 ==> k + j == n/2;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}