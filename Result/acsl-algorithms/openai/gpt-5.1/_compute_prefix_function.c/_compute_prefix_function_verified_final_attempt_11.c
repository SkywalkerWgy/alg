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
        loop invariant i_0: 1 <= i <= n;

        loop invariant i_1: n > 0;

        loop invariant i_2: \valid_read(s);

        loop invariant i_3: \valid_read(pi);

        loop invariant i_4: \valid(s + (0..n - 1));

        loop invariant i_5: \valid(pi + (0..n - 1));

        loop invariant i_6: \separated(&pi[0..(n - 1)], &s[0..(n - 1)]);

        loop invariant i_7: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

        loop invariant i_8: \forall integer k; i <= k < n ==> pi[k] == 0;

        loop invariant i_36: \forall integer k; 0 <= k < i ==> 0 <= pi[k];

        loop invariant i_40: \forall integer k; 0 <= k < i ==> 0 <= pi[k] <= k;


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++) {
        int j = pi[i - 1];
        // Loop B
        /*@
            loop invariant i_9: 1 <= i < n;

            loop invariant i_10: \valid_read(s);

            loop invariant i_11: \valid_read(pi);

            loop invariant i_12: \valid(s + (0..n - 1));

            loop invariant i_13: \valid(pi + (0..n - 1));

            loop invariant i_14: \separated(&pi[0..(n - 1)], &s[0..(n - 1)]);

            loop invariant i_15: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

            loop invariant i_16: \forall integer k; i <= k < n ==> pi[k] == 0;

            loop invariant i_18: pre_post(s, i - 1, j);

            loop invariant i_22: j == pi[i - 1] ==> \forall integer t; j < t <= pi[i - 1] ==> pre_post_not(s, i, t);

            loop invariant i_23: \forall integer t; j < t <= pi[i - 1] ==> 0 == 0;

            loop invariant i_24: \forall integer t; j < t <= pi[i - 1] ==> 1 == 1;

            loop invariant i_25: j == pi[i - 1] ==> \forall integer t; j < t <= pi[i - 1] ==> 1 == 1;

            loop invariant i_26: j == j;

            loop invariant i_28: \forall integer t; j < t <= pi[i - 1] ==> t > j;

            loop invariant i_29: 0 <= j;

            loop invariant i_30: j <= pi[i - 1];

            loop invariant i_32: j >= 0;

            loop invariant i_33: \forall integer t; (j < t && t <= pi[i - 1]) ==> pre_post_not(s, i, t);

            loop invariant i_34: \forall integer t; j < t <= j ==> pre_post_not(s, i, t);

            loop invariant i_35: \forall integer t; (j < t && t <= j) ==> pre_post_not(s, i, t);

            loop invariant i_37: 0 <= j <= pi[i - 1];

            loop invariant i_38: pre_post(s, i - 1, pi[i - 1]);

            loop invariant i_39: 0 <= j <= i;

            loop invariant i_41: j == 0 || pre_post(s, j - 1, pi[j - 1]);

            loop invariant i_42: j <= i - 1;

            loop invariant i_43: \forall integer t; (j < t && t <= pi[i - 1]) ==> t == t;

            loop invariant i_44: \forall integer t; (j < t && t <= pi[i - 1]) ==> t <= i - 1;

            loop invariant i_45: \forall integer t; (j < t && t <= pi[i - 1]) ==> (pre_post_not(s, i, t) || !pre_post_not(s, i, t));


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