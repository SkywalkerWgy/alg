#define m 10
#define n 10

/*@
    predicate is_max(integer a, integer b, integer result) =
        result >= a && 
        result >= b && 
        (result == a || result == b);
*/

/*@
    assigns \nothing;
    ensures is_max(a, b, \result);
*/
int max(int a, int b) {
  int max_val = a >= b ? a : b;
  return max_val;
}

/*@
    requires \valid_read(s);
    requires \valid_read(t);
    requires \valid(s+(0..(m - 1)));
    requires \valid(t+(0..(n - 1)));
    requires \valid(dp + (0..(m)));
    requires \valid(dp[0..(m)] + (0..(n)));
    requires \forall integer k; 0 <= k <= n ==> dp[0][k] == 0;
    requires \forall integer k; 0 <= k <= m ==> dp[k][0] == 0;
    ensures e_1: \forall integer k; 0 <= k <= n ==> dp[0][k] == 0;
    ensures e_2: \forall integer k; 0 <= k <= m ==> dp[k][0] == 0;
    ensures e_3: \forall integer p, q; 1 <= p <= m && 1 <= q <= n ==> s[p - 1] == t[q - 1] && dp[p][q] == dp[p - 1][q - 1] + 1 || is_max(dp[p - 1][q], dp[p][q - 1], dp[p][q]);
    assigns dp[0..(m)][0..(n)];
*/
int _lcs(const char *s, const char *t, int dp[m + 1][n + 1]) {
    int i = 1, j = 1;
    // Loop A
    /*@
        loop invariant i_0: \exists integer k; 0 <= k < i && dp[k][0] == 0;

        loop invariant i_1: \exists integer k; 0 <= k < i && dp[k][j] == dp[k][j-1];


        loop assigns dp[1..(m)][1..(n)], i, j;
    */
    for (i = 1; i <= m; i++) {
        // Loop B
        /*@
            loop invariant i_2: \exists integer k; 0 <= k < i && dp[k][0] == 0;

            loop invariant i_3: \exists integer k; 0 <= k < i && dp[k][j] == dp[k][j-1];


            loop assigns dp[i][1..(n)], j;
        */
        for (j = 1; j <= n; j++) {
            if (s[i - 1] == t[j - 1]){
                dp[i][j] = dp[i - 1][j - 1] + 1;
            }
            else{
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1]);
            }
        }
    }
    return dp[m][n];
}