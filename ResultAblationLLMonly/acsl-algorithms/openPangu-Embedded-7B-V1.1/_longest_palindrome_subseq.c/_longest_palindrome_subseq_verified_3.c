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
    requires \valid(dp + (0..(n - 1)));
    requires \valid(dp[0..(n - 1)] + (0..(n - 1)));
    requires \forall integer i, j; 0 <= i < n && 0 <= j < n && i != j ==> \separated(&dp[i] + (0..(n - 1)), &dp[j] + (0..(n - 1)), &s[0..(n - 1)]);
    requires \forall integer i, j; 0 <= i < n && 0 <= j < n ==> dp[i][j] == 0;
    ensures e_1: \forall integer p, q; -1 < p < n && p < q < n ==> 
                (s[p] == s[q] && dp[p][q] == dp[p + 1][q - 1] + 2) || (is_max(dp[p + 1][q], dp[p][q - 1], dp[p][q]));
    assigns dp[0..(n - 1)][0..(n - 1)];
*/
int _longest_palindrome_subseq(char* s, int dp[n][n]) {
    // Loop A
    /*@
        loop invariant i_16: : \forall i; 0 <= i < n;

        loop invariant i_17: : \forall i, j; 0 <= i < j < n;

        loop invariant i_18: : \forall i, j; dp[i][j] >= 0;


        loop assigns dp[0..(n - 1)][0..(n - 1)], i;
    */
    for (int i = n - 1; i >= 0; i--) {
        dp[i][i] = 1;
        char c1 = s[i];
        // Loop B
        /*@
            loop invariant i_19: \forall i, j; 0 <= i < n && 0 <= j < n ==> dp[i][j] >= 0;

            loop invariant i_20: \forall i; 0 <= i < n && \forall j; 0 <= j < n && i != j ==> dp[i][j] >= 0;


            loop assigns dp[i][(i + 1)..(n - 1)], j;
        */
        for (int j = i + 1; j < n; j++) {
            char c2 = s[j];
            if (c1 == c2) {
                dp[i][j] = dp[i + 1][j - 1] + 2;
            } else {
                dp[i][j] = max(dp[i + 1][j], dp[i][j - 1]);
            }
        }
    }
    return dp[0][n - 1];
}