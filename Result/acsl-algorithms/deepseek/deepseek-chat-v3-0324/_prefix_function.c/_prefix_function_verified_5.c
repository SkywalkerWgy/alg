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
    requires \valid(s + (0..i));
    requires 0 < j <= i;
    requires i > 0;
    ensures \result == 1 ==> pre_post(s, i, j);
    ensures \result == 0 ==> pre_post_not(s, i, j);
    assigns \nothing;
*/
int substr(char* s, int i, int j){
    /*@
        loop invariant 0 <= k <= j;
        loop invariant \forall integer p; 0 <= p < k ==> s[p] == s[i - j + 1 + p];
        loop assigns k;
    */
    for(int k = 0; k < j; k++){
        if(s[k] == s[i - j + 1 + k]){
            continue;
        }
        else{
            return 0;
        }
    }
    return 1;
}

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
void _prefix_function(char* s, int* pi, int n) {
    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= n;

        loop invariant i_1: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

        loop invariant i_2: \forall integer k; i <= k < n ==> pi[k] == 0;

        loop invariant i_7: \forall integer k; 0 <= k < i ==> pi[k] <= k;

        loop invariant i_11: \forall integer k; 1 <= k < i ==> !pre_post(s, k, k+1);

        loop invariant i_13: \forall integer k; 0 <= k < i ==> pi[k] < k || pi[k] == 0;

        loop invariant i_14: \forall integer k; 0 <= k < i ==> (pi[k] > 0) ==> pre_post(s, k, pi[k]);

        loop invariant i_16: \forall integer k; 0 <= k < i ==> pi[k] <= k && (pi[k] > 0 ==> pre_post(s, k, pi[k]));

        loop invariant i_18: \forall integer k; 1 <= k < i ==> !pre_post(s, k, k+1) || pi[k] < k;

        loop invariant i_19: \forall integer k; 1 <= k < i ==> pi[k] != k;


        loop assigns i, pi[1..(n - 1)];
    */
    for (int i = 1; i < n; i++){
        // Loop B
        /*@
            loop invariant i_3: 0 <= j <= i;

            loop invariant i_4: \forall integer k; j < k <= i ==> !pre_post(s, i, k);

            loop invariant i_5: j == i ==> \forall integer k; 1 <= k <= i ==> !pre_post(s, i, k);

            loop invariant i_6: \forall integer k; 0 <= k < j ==> !pre_post(s, i, k) || k == pi[i];

            loop invariant i_8: j == i ==> \forall integer k; 1 <= k <= i ==> !pre_post(s, i, k) || k == pi[i];

            loop invariant i_9: \forall integer k; 0 <= k < i ==> pre_post(s, k, pi[k]);

            loop invariant i_12: \forall integer k; 0 <= k < i ==> pi[k] <= k;

            loop invariant i_15: \forall integer k; 0 <= k < i ==> pi[k] <= k && (pi[k] > 0 ==> pre_post(s, k, pi[k]));

            loop invariant i_17: \forall integer k; 0 <= k < j ==> !pre_post(s, i, k+1);

            loop invariant i_20: j == pi[i] ==> pre_post(s, i, j);

            loop invariant i_21: \forall integer k; 0 <= k < i ==> (pi[k] > 0) ==> pre_post(s, k, pi[k]);


            loop assigns j, pi[i];
        */
        for (int j = i; j > 0; j--){
            if (substr(s, i, j) == 1) {
                pi[i] = j;
                break;
            }
        }
    }
}