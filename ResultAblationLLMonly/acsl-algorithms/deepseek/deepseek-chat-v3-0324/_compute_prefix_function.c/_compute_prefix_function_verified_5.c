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
        loop invariant i_0: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

        loop invariant i_1: 0 <= i <= n;

        loop invariant i_2: i > 0 ==> pi[i - 1] == j;

        loop invariant i_3: \forall integer k; i <= k < n ==> pi[k] == 0;

        loop invariant i_9: s for Loop A: ``` loop invariant \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

        loop invariant i_10: \separated(&pi[0..(n - 1)], &s[0..(n - 1)]);


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        // Loop B
        /*@
            loop invariant i_4: s for Loop B: ``` loop invariant pre_post(s, i, j);

            loop invariant i_5: pre_post(s, i, j);

            loop invariant i_6: j >= 0;

            loop invariant i_7: j <= pi[i - 1];

            loop invariant i_8: \forall integer k; j < k <= pi[i - 1] ==> pre_post_not(s, i, k);

            loop invariant i_11: j <= pi[i-1];

            loop invariant i_12: \forall integer k; j < k <= pi[i-1] ==> pre_post_not(s, i, k);

            loop invariant i_13: \forall integer k; 0 <= k < j ==> s[k] == s[i - j + k];

            loop invariant i_14: \forall integer k; j < k <= pi[i-1] ==> \exists integer m; 0 <= m < k && s[m] != s[i - k + m];

            loop invariant i_15: s for Loop B: ``` loop invariant j >= 0;


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