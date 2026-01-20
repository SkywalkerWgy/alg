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
        loop invariant i_0: -1 <= i < n;

        loop invariant i_1: \valid_read(s);

        loop invariant i_2: \valid(dp + (0..(n - 1)));

        loop invariant i_3: \valid(dp[0..(n - 1)] + (0..(n - 1)));

        loop invariant i_4: \forall integer r1, r2; 0 <= r1 < n && 0 <= r2 < n && r1 != r2 ==> \separated(&dp[r1] + (0..(n - 1)), &dp[r2] + (0..(n - 1)), &s[0..(n - 1)]);

        loop invariant i_5: \forall integer p; i < p < n ==> dp[p][p] == 1;

        loop invariant i_6: \forall integer p, q; i < p < n && p < q < n ==> (s[p] == s[q] && dp[p][q] == dp[p + 1][q - 1] + 2) || (is_max(dp[p + 1][q], dp[p][q - 1], dp[p][q]));


        loop assigns dp[0..(n - 1)][0..(n - 1)], i;
    */
    for (int i = n - 1; i >= 0; i--) {
        dp[i][i] = 1;
        char c1 = s[i];
        // Loop B
        /*@
            loop invariant i_7: j >= i + 1 && j <= n;

            loop invariant i_8: \valid_read(s);

            loop invariant i_9: \valid(dp + (0..(n - 1)));

            loop invariant i_10: \valid(dp[0..(n - 1)] + (0..(n - 1)));

            loop invariant i_11: \forall integer r1, r2; 0 <= r1 < n && 0 <= r2 < n && r1 != r2 ==> \separated(&dp[r1] + (0..(n - 1)), &dp[r2] + (0..(n - 1)), &s[0..(n - 1)]);

            loop invariant i_12: dp[i][i] == 1;

            loop invariant i_13: \forall integer p; i < p < n ==> dp[p][p] == 1;

            loop invariant i_14: \forall integer p, q; i < p < n && p < q < n ==> (s[p] == s[q] && dp[p][q] == dp[p + 1][q - 1] + 2) || is_max(dp[p + 1][q], dp[p][q - 1], dp[p][q]);

            loop invariant i_15: \forall integer k; i < k < j ==> (s[i] == s[k] && dp[i][k] == dp[i + 1][k - 1] + 2) || is_max(dp[i + 1][k], dp[i][k - 1], dp[i][k]);


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