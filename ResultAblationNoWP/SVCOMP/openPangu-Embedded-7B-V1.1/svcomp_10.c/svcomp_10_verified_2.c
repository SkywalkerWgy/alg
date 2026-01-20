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
        loop invariant i_4: k >= n;

        loop invariant i_5: i <= n;


        loop assigns i, k;
    */
    while( i < n ) {
        k--;
        i = i + 2;
    }

    int j = 0;
    
    // Loop B
    /*@
        loop invariant i_6: k >= n;

        loop invariant i_7: i <= n;

        loop invariant i_8: k > 0 && i < n;

        loop invariant i_9: k >= 1;

        loop invariant i_10: j <= n / 2;


        loop assigns j, k;
    */
    while( j < n / 2 ) {
        //@ assert k > 0;
        k--;
        j++;
    }
    return 0;
}