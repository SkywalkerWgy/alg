/*@
    predicate pre_post(char* s, integer i, integer j) =
        j == 0 || \forall integer k; 0 <= k < j ==> s[k] == s[i - j + 1 + k];
*/

/*@
    predicate pre_post_not(char* s, integer i, integer j) =
        \exists integer k; 0 <= k < j && s[k] != s[i - j + 1 + k];
*/

/*@
    requires \valid_read(s);
    requires \valid_read(pi);
    requires \valid(s + (0..n - 1));
    requires \valid(pi + (0..n - 1));
    requires \separated(&pi[0..(n - 1)], &s[0..(n - 1)]);
    requires \forall integer k; 0 <= k < n ==> pi[k] == 0;
    requires n > 0;
    assigns pi[0..(n - 1)];
    ensures e_1: \forall integer k; 0 <= k < n ==> pre_post(s, k, pi[k]);
*/
void _compute_prefix_function(char* s, int* pi, int n) {
    // Loop A
    /*@
        loop invariant i_10: 1 <= i <= n-1;

        loop invariant i_11: 0 <= pi[i-1] <= i;

        loop invariant i_12: j <= i;

        loop invariant i_13: s[i] == s[pi[i-1] - 1];

        loop invariant i_14: \forall integer k; 0 <= k < pi[i-1] ==> s[k] == s[i - pi[i-1] + 1 + k];

        loop invariant i_15: \forall integer j; 0 <= j < i ==> pi[j] == 0 || (pi[j] > 0 && s[j] == s[i - j]);

        loop invariant i_16: 1 <= j <= pi[i-1];

        loop invariant i_17: 0 <= pi[j-1] <= j;

        loop invariant i_18: s[i] == s[pi[j-1] - 1];

        loop invariant i_19: \forall integer k; 0 <= k < pi[j-1] ==> s[k] == s[i - pi[j-1] + 1 + k];

        loop invariant i_20: \forall integer j; 0 <= j < j <= pi[j-1] ==> pi[j] == 0 || (pi[j] > 0 && s[j] == s[i - j]);


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        // Loop B
        /*@
            loop invariant i_21: 1 <= i <= n-1;

            loop invariant i_22: 0 <= pi[i-1] <= i;

            loop invariant i_23: j <= i;

            loop invariant i_24: s[i] == s[pi[i-1] - 1];

            loop invariant i_25: \forall integer k; 0 <= k < pi[i-1] ==> s[k] == s[i - pi[i-1] + 1 + k];

            loop invariant i_26: 1 <= j <= pi[i-1];

            loop invariant i_27: \forall integer j; 0 <= j < i ==> pi[j] == 0 || (pi[j] > 0 && s[j] == s[i - j]);

            loop invariant i_28: j >= 0;

            loop invariant i_29: \forall integer k; 0 <= k < j ==> s[k] == s[i - pi[k-1] + 1 + k];

            loop invariant i_30: 1 <= j <= pi[j-1];

            loop invariant i_31: \forall integer k; 0 <= k < pi[j-1] ==> s[k] == s[i - pi[k-1] + 1 + k];

            loop invariant i_32: \forall integer j; 0 <= j < j <= pi[j-1] ==> pi[j] == 0 || (pi[j] > 0 && s[j] == s[i - j]);

            loop invariant i_33: s[i] == s[pi[j-1] - 1];


            loop assigns j;
        */
        while (j > 0 && s[i] != s[j]){
            if (s[i] == s[j]){
                j++;
                pi[i] = j;
                break;
            }
            else{
                j = pi[j - 1];
            }
        }
    }
}