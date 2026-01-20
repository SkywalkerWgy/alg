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
        loop invariant i_34: 1 <= i <= n;

        loop invariant i_35: j >= 0;

        loop invariant i_36: \forall integer k; 0 <= k < j < i ==> pi[k] == s[i] == s[k];

        loop invariant i_37: \forall integer k; 0 <= k < j && s[k] != s[j] ==> true;


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        // Loop B
        /*@
            loop invariant i_38: 1 <= i <= n;

            loop invariant i_39: j >= 0;

            loop invariant i_40: \forall integer k; 0 <= k < j < i ==> pi[k] == s[i] == s[k];

            loop invariant i_41: \forall integer k; 0 <= k < j && s[k] != s[j] ==> true;

            loop invariant i_42: \exists integer k; 0 <= k < j && s[k] == s[j];


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