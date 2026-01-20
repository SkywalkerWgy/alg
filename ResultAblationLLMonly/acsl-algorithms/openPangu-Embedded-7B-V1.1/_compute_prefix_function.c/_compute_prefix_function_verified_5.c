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
        loop invariant i_43: 1 <= i <= n;

        loop invariant i_44: 1 <= j <= i+1;

        loop invariant i_45: s[i] == s[j];

        loop invariant i_46: pi[i] == j;

        loop invariant i_47: 0 <= j < n;

        loop invariant i_48: j >= 0;

        loop invariant i_49: i < n;

        loop invariant i_50: \exists index; 0 <= index < i ==> pi[index] == j;

        loop invariant i_51: j < n;

        loop invariant i_52: \exists k; 0 <= k < j ==> s[k] == s[i - j + 1 + k];


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        // Loop B
        /*@
            loop invariant i_53: 1 <= i <= n;

            loop invariant i_54: 1 <= j <= i+1;

            loop invariant i_55: s[i] == s[j];

            loop invariant i_56: pi[i] == j;

            loop invariant i_57: 0 <= j < n;

            loop invariant i_58: j >= 0;

            loop invariant i_59: i < n;

            loop invariant i_60: \exists index; 0 <= index < i ==> pi[index] == j;

            loop invariant i_61: j < n;

            loop invariant i_62: \exists k; 0 <= k < j ==> s[k] == s[i - j + 1 + k];

            loop invariant i_63: 1 <= j <= n;

            loop invariant i_64: j >= 1;

            loop invariant i_65: pi[j] == i;

            loop invariant i_66: \exists k; 0 <= k < j;

            loop invariant i_67: \exists index; 0 <= index < j;

            loop invariant i_68: \forall integer k; 0 <= k < j ==> pi[k] == i;

            loop invariant i_69: \exists m; 0 <= m < i;


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