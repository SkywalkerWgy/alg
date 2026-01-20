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
        loop invariant i_14: s for Loop A: ``` loop invariant 1 <= i <= n;

        loop invariant i_15: 1 <= i <= n;

        loop invariant i_16: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

        loop invariant i_17: \forall integer k; i <= k < n ==> pi[k] == 0;

        loop invariant i_18: \valid_read(s);

        loop invariant i_19: \valid_read(pi);

        loop invariant i_20: \valid(s + (0..n - 1));

        loop invariant i_21: \valid(pi + (0..n - 1));

        loop invariant i_22: \separated(&pi[0..(n - 1)], &s[0..(n - 1)]);


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        // Loop B
        /*@
            loop invariant i_23: s for Loop B: ``` loop invariant 0 <= j <= pi[i-1];

            loop invariant i_24: 0 <= j <= pi[i-1];

            loop invariant i_25: pre_post_not(s, i, j) || j == 0;

            loop invariant i_26: \forall integer k; 0 <= k < j ==> s[k] == s[i - j + k];

            loop invariant i_27: \valid_read(s);

            loop invariant i_28: \valid_read(pi);

            loop invariant i_29: \valid(s + (0..n - 1));

            loop invariant i_30: \valid(pi + (0..n - 1));

            loop invariant i_31: \separated(&pi[0..(n - 1)], &s[0..(n - 1)]);


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