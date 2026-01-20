# define INT_MAX 2147483647
# define INT_MIN -2147483648
/*@
    requires INT_MIN < n && n < INT_MAX;
    requires INT_MIN < m && m < INT_MAX;
    requires INT_MIN < l && l < INT_MAX;
*/
int svcomp_17(int n, int m , int l) {
    int i, j, k;

    if(3 * n <= m + l); else goto END;
    
    // Loop A
    /*@
        loop invariant i_0: 0 <= i && i <= n;

        loop invariant i_1: 3 * n <= m + l;


        loop assigns k;
        loop assigns j;
        loop assigns i;
    */
    for (i=0;i<n;i++)
        /*@
            loop assigns k;
            loop assigns j;
            loop assigns i;
        */
        for (j = 2*i;j<3*i;j++)
            /*@
                loop assigns k;
            */
            for (k = i; k< j; k++) {
                //@ assert k-i <= 2*n ;
            }
END:
    return 0;
}