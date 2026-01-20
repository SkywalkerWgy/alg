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
        loop invariant i_0: \valid_read(t);

        loop invariant i_1: \valid_read(p);

        loop invariant i_2: \valid(t + (0..n - 1));

        loop invariant i_3: \valid(p + (0..m - 1));

        loop invariant i_4: \separated(&t[0..(n - 1)], &p[0..(m - 1)]);

        loop invariant i_5: n > 0;

        loop invariant i_6: m > 0;

        loop invariant i_7: 0 <= j <= m;

        loop invariant i_8: \forall integer k; 0 <= k < j ==> p[k] == t[match + k];


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
