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
    ensures e_1: \result == 1 ==> string_same(t, p, n, m, match);
*/
int _string_same_judge(char* t, char* p, int n, int m, int match){
    // Loop A
    /*@
        loop invariant i_8: m > 0;

        loop invariant i_9: \forall integer j; 0 <= j < m && p[j] == t[match + j];

        loop invariant i_10: \exists integer k; 0 <= k < m && \forall integer \ell; \ell < m ==> p[\ell] == t[match + \ell];

        loop invariant i_11: \forall integer j; 0 <= j < m;

        loop invariant i_12: \forall integer j; 0 <= match + j < n;

        loop invariant i_13: \forall integer j; t[match + j] == p[j];

        loop invariant i_14: \forall integer j; 0 <= match + j <= n - 1;

        loop invariant i_15: \forall integer j; \forall integer k; 0 <= k < n ==> \forall integer \ell; 0 <= \ell < m && p[\ell] == t[match + \ell];

        loop invariant i_16: \exists integer k; 0 <= k < m && \forall integer \ell; \ell < n && t[match + \ell] == p[\ell];


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
