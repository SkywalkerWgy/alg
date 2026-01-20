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
        loop invariant i_7: \forall integer p, q; i < p < n && p <= q < n ==> dp[p][q] == \at(dp[p][q], Pre);

        loop invariant i_8: \forall integer p, q; i <= p < n && p <= q < n && (p > i || q < p) ==> dp[p][q] == 0;

        loop invariant i_9: \forall integer p; i <= p < n ==> dp[p][p] == 1;

        loop invariant i_10: \forall integer p, q; i <= p < q < n ==> (s[p] == s[q] && dp[p][q] == dp[p + 1][q - 1] + 2) || (is_max(dp[p + 1][q], dp[p][q - 1], dp[p][q]));


        loop assigns dp[0..(n - 1)][0..(n - 1)], i;
    */
    for (int i = n - 1; i >= 0; i--) {
        dp[i][i] = 1;
        char c1 = s[i];
        // Loop B
        /*@
            loop invariant i_11: s for Loop B: ``` loop invariant i_7: \forall integer p, q; i < p < n && p <= q < n ==> dp[p][q] == \at(dp[p][q], Pre);

            loop invariant i_12: \forall integer p, q; i < p < n && p <= q < n ==> dp[p][q] == \at(dp[p][q], Pre);

            loop invariant i_13: \forall integer p, q; i <= p < n && p <= q < n && (p > i || q < j) ==> dp[p][q] == 0;

            loop invariant i_14: \forall integer p; i <= p < n ==> dp[p][p] == 1;

            loop invariant i_15: \forall integer p, q; i <= p < q < j && p < q ==> ((s[p] == s[q] && dp[p][q] == dp[p + 1][q - 1] + 2) || (is_max(dp[p + 1][q], dp[p][q - 1], dp[p][q])));

            loop invariant i_16: \forall integer q; i <= q < j ==> (s[i] == s[q] && dp[i][q] == dp[i + 1][q - 1] + 2) || (is_max(dp[i + 1][q], dp[i][q - 1], dp[i][q]));


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