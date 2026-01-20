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
    ensures \forall integer k; 0 <= k < n ==> pre_post(s, k, pi[k]);
*/
void _compute_prefix_function(char* s, int* pi, int n) {
    /*@
        loop invariant 1 <= i <= n;
        loop invariant pi[0] == 0;
        loop invariant \forall integer k; i <= k < n ==> pi[k] == 0;
        loop invariant i0: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);
        loop invariant i1: \forall integer k; 0 <= k < n ==> 0 <= pi[k] < n;
        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        /*@
            loop invariant i2: 0 <= j < n;
            loop invariant 1 <= i <= n;
            loop invariant pi[0] == 0;
            loop invariant \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);
            loop invariant \forall integer k; i <= k < n ==> pi[k] == 0;
            loop invariant \forall integer k; 0 <= k < n ==> 0 <= pi[k] < n;
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