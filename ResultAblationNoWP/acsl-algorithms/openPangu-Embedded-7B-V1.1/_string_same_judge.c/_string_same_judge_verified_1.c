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
        loop invariant i_0: m >= 0 && n > 0;

        loop invariant i_1: \forall integer j; 0 <= j < m ==> p[j] == t[match + j];

        loop invariant i_2: \exists integer k; 0 <= k < n && t[k] == p[0];

        loop invariant i_3: \forall integer j; 0 <= j < m ==> \separated(&t[0..(n - 1)], &p[0..(m - 1)]);

        loop invariant i_4: true;


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
