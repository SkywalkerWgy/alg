#define m 10
#define n 10

/*@
    predicate is_min3(integer a, integer b, integer c, integer result) =
        result <= a && 
        result <= b && 
        result <= c &&
        (result == a || result == b || result == c);
*/


/*@
    assigns \nothing;
    ensures is_min3(a, b, c, \result);
*/
int min3(int a, int b, int c) {
  int min_val = a;
  if (b < min_val) min_val = b;
  if (c < min_val) min_val = c;
  return min_val;
}


/*@
    requires \valid_read(s);
    requires \valid_read(t);
    requires \valid(s+(0..(m - 1)));
    requires \valid(t+(0..(n - 1)));
    requires \valid(dp + (0..(m)));
    requires \valid(dp[0..(m)] + (0..(n)));
    requires \forall integer i, j; 0 <= i <= m && 0 <= j <= m && i != j ==> \separated(&dp[i] + (0..(n)), &dp[j] + (0..(n)), &s[0..(n - 1)], &t);
    requires \forall integer k; 0 <= k <= n ==> dp[0][k] == k;
    requires \forall integer k; 0 <= k <= m ==> dp[k][0] == k;
    ensures e_1: \forall integer k; 0 <= k <= n ==> dp[0][k] == k;
    ensures e_2: \forall integer k; 0 <= k <= m ==> dp[k][0] == k;
    ensures e_3: \forall integer p, q; 1 <= p <= m && 1 <= q <= n ==> is_min3(dp[p - 1][q - 1] + (s[p - 1] == t[q - 1] ? 0 : 1), dp[p - 1][q] + 1, dp[p][q - 1] + 1, dp[p][q]);
    assigns dp[0..(m)][0..(n)];
*/
int _edit_distance(const char *s, const char *t, int dp[m + 1][n + 1]) {
    int i = 1, j = 1;

    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= m && 1 <= j <= n;

        loop invariant i_1: \forall integer k; 0 <= k < i ==> dp[k][0] == k;


        loop assigns dp[1..(m)][1..(n)], i, j;
    */
    for (i = 1; i <= m; i++) {
        // Loop B
        /*@
            loop invariant i_11: 1 <= j <= n;

            loop invariant i_12: \forall integer k; 0 <= k < j ==> dp[0][k] == k;

            loop invariant i_13: \forall integer k; 0 <= k < j ==> dp[0][k] <= dp[0][j];

            loop invariant i_15: \forall integer k; 0 <= k < j && 0 <= l < n ==> dp[j][l] >= dp[0][k] + (j - k);

            loop invariant i_16: 1 <= i <= m && 1 <= j <= n;

            loop invariant i_17: \forall integer k; 0 <= k < i ==> dp[k][0] == k;

            loop invariant i_18: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] == min3(dp[i-1][l-1] + (s[i-1]==t[l-1]?0:1), dp[i-1][l] + 1, dp[i][l-1] + 1);

            loop invariant i_19: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] <= dp[i][n];

            loop invariant i_20: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] >= dp[i][l-1] + 1;

            loop invariant i_21: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] >= dp[k][l] + (i - k);

            loop invariant i_22: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] >= dp[m][n];

            loop invariant i_23: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] >= dp[0][0];

            loop invariant i_24: \forall integer k; 0 <= k < i && 0 <= l < n ==> dp[i][l] <= dp[k][l] + (l - k);


            loop assigns dp[i][1..(n)], j;
        */
        for (j = 1; j <= n; j++) {
            dp[i][j] = min3(dp[i - 1][j - 1] + (s[i - 1] == t[j - 1] ? 0 : 1), dp[i - 1][j] + 1, dp[i][j - 1] + 1);
        }
    }
    return dp[m][n];
}