/*@
    predicate string_same(char* t, char* p, integer n, integer m, integer match) =
        n < m || \forall integer k; 0 <= k < m ==> p[k] == t[match + k];
*/

/*@
    requires \valid_read(t);
    requires \valid_read(p);
    requires \valid(t + (0..n - 1));
    requires \valid(p + (0..m - 1));
    requires \separated(&t[0..(n - 1)], &p[0..(m - 1)]);
    requires n > 0;
    requires m > 0;
    assigns \nothing;
    ensures \result == 1 ==> string_same(t, p, n, m, match);
*/
int _string_same_judge(char* t, char* p, int n, int m, int match){
    /*@
        loop invariant 0 <= j <= m;
        loop invariant \forall integer q; 0 <= q < j ==> p[q] == t[match + q];
        loop assigns j;
    */
    for (int j = 0; j < m; j++){
        if (p[j] == t[match + j]) {
            continue;
        }
        else{
            return 0;
        }
    }
    return 1;
}

/*@
    requires \valid_read(t);
    requires \valid_read(p);
    requires \valid(t + (0..n - 1));
    requires \valid(p + (0..m - 1));
    requires \separated(&t[0..(n - 1)], &p[0..(m - 1)]);
    requires n > 0;
    requires m > 0;
    assigns \nothing;
    ensures \result == -1 || string_same(t, p, n, m, \result);
*/
int _naive_string_matcher(char* t, char* p, int m, int n) {
    if(n < m){
        return -1;
    }
    // Loop A
    /*@
        loop invariant i_0: 0 <= i <= n - m;

        loop invariant i_1: \forall integer k; 0 <= k < i ==> !string_same(t, p, n, m, k);

        loop invariant i_13: \forall integer k; 0 <= k < i ==> \forall integer l; 0 <= l < m ==> p[l] != t[k + l];

        loop invariant i_26: \forall integer i; 0 <= i < n - m ==> \forall integer k; 0 <= k < m ==> p[k] != t[i + k] || !string_same(t, p, n, m, i);

        loop invariant i_30: \forall integer k; 0 <= k < i ==> \exists integer l; 0 <= l < m ==> p[l] != t[k + l];

        loop invariant i_31: \forall integer i; 0 <= i < n - m ==> \forall integer k; 0 <= k < m ==> p[k] != t[i + k] || \exists integer l; 0 <= l < k ==> p[l] != t[i + l];


        loop assigns i;
    */
    for (int i = 0; i < n - m; i++){
        // Loop B
        /*@
            loop invariant i_2: 0 <= j <= m;

            loop invariant i_3: \forall integer k; 0 <= k < j ==> !string_same(t, p, n, m, k);

            loop invariant i_4: \forall integer k; 0 <= k < j ==> p[k] != t[i + k];

            loop invariant i_5: \forall integer k; 0 <= k < i ==> !string_same(t, p, n, m, k);

            loop invariant i_6: \forall integer l; 0 <= l < j ==> p[l] == t[i + l] ==> !string_same(t, p, n, m, l);

            loop invariant i_8: \forall integer k; 0 <= k < j ==> !string_same(t, p, n, m, i);

            loop invariant i_10: \forall integer s; 0 <= s < i ==> !string_same(t, p, n, m, s);

            loop invariant i_11: \forall integer l; 0 <= l < j ==> p[l] == t[i + l];

            loop invariant i_12: \forall integer k; j <= k < m ==> !string_same(t, p, n, m, i);

            loop invariant i_14: \forall integer k; j <= k < m ==> \exists integer l; 0 <= l < j ==> p[l] != t[i + l];

            loop invariant i_16: \forall integer k; j <= k < m ==> \exists integer l; 0 <= l < k ==> p[l] != t[i + l];

            loop invariant i_18: \forall integer k; j <= k < m ==> \exists integer l; 0 <= l < m ==> p[l] != t[i + l];

            loop invariant i_19: \forall integer k; 0 <= k < j ==> p[k] == t[i + k] ==> !string_same(t, p, n, m, i);

            loop invariant i_20: \forall integer k; 0 <= k < j ==> p[k] != t[i + k] ==> !string_same(t, p, n, m, i);

            loop invariant i_21: \forall integer k; 0 <= k < j ==> string_same(t, p, n, m, i) ==> p[k] == t[i + k];

            loop invariant i_22: j == 0 ==> \forall integer k; 0 <= k < m ==> p[k] != t[i + k];

            loop invariant i_23: j > 0 ==> \forall integer k; 0 <= k < j - 1 ==> p[k] == t[i + k];

            loop invariant i_24: j == 0 ==> \forall integer k; 0 <= k < m ==> !string_same(t, p, n, m, i);

            loop invariant i_25: j > 0 ==> \forall integer k; 0 <= k < j ==> p[k] == t[i + k];

            loop invariant i_28: j == 0 || \forall integer k; 0 <= k < j ==> p[k] == t[i + k];

            loop invariant i_29: \forall integer k; j <= k < m ==> \exists integer l; 0 <= l < j + 1 ==> p[l] != t[i + l];

            loop invariant i_32: j == 0 ==> \forall integer k; 0 <= k < m ==> \exists integer l; 0 <= l < k ==> p[l] != t[i + l];

            loop invariant i_33: j == m ==> string_same(t, p, n, m, i);

            loop invariant i_34: j < m ==> \exists integer k; j <= k < m ==> p[k] != t[i + k];

            loop invariant i_36: j == 0 ==> \forall integer k; 0 <= k < m ==> p[k] != t[i + k] || \exists integer l; 0 <= l < k ==> p[l] != t[i + l];

            loop invariant i_37: j <= m && (j == m ==> string_same(t, p, n, m, i));

            loop invariant i_38: j == 0 ==> \forall integer k; 0 <= k < m ==> \exists integer l; 0 <= l < k ==> p[l] != t[i + k];


            loop assigns j;
        */
        for (int j = 0; j < m; j++){
            if(_string_same_judge(t, p, n, m, j) == 1){
                return j;
            }
        }
    }
    return -1;
}