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
        loop invariant i_0: INT_MIN < n && n < INT_MAX;

        loop invariant i_1: INT_MIN < m && m < INT_MAX;

        loop invariant i_2: INT_MIN < l && l < INT_MAX;

        loop invariant i_3: 3 * n <= m + l;

        loop invariant i_4: 0 <= i;

        loop invariant i_5: n < 0 ==> i == 0;

        loop invariant i_6: n >= 0 ==> i <= n;

        loop invariant i_7: INT_MIN < n && n < INT_MAX && INT_MIN < m && m < INT_MAX && INT_MIN < l && l < INT_MAX && 3 * n <= m + l;

        loop invariant i_8: (n < 0 ==> i == 0) && (n >= 0 ==> 0 <= i <= n);

        loop invariant i_9: INT_MIN < n && INT_MIN < m && INT_MIN < l;

        loop invariant i_10: n < INT_MAX && m < INT_MAX && l < INT_MAX;

        loop invariant i_11: m + l >= 3 * n;

        loop invariant i_12: (n < 0 && i == 0) || (n >= 0 && 0 <= i && i <= n);

        loop invariant i_13: (0 <= i && i <= n) || (n < 0 && i == 0);

        loop invariant i_14: n >= 0 ==> 0 <= i;

        loop invariant i_15: i >= 0;

        loop invariant i_16: (n <= 0 ==> i == 0) && (n > 0 ==> 0 <= i && i <= n);

        loop invariant i_17: i < INT_MAX;

        loop invariant i_18: (n <= 0 && i == 0) || (n > 0 && 0 <= i && i <= n);


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