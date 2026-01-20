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
        loop invariant i_0: i + k == n && i % 2 == 0;

        loop invariant i_1: k >= 0 && j == n - i;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_2: i >= 0 && i < n && k >= 0 && j == n - i;

        loop invariant i_3: k >= 0 && j == n - i;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}