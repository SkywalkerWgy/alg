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
        loop invariant i_19: && 0..m == 1;

        loop invariant i_20: j == 0 || p[j] == t[match + j];

        loop invariant i_21: \forall integer i; 0 <= i < j ==> p[i] == t[match + i];

        loop invariant i_22: \exists integer k; 0 <= k < j && p[k] == t[match + k];

        loop invariant i_23: 1 == 1;

        loop invariant i_24: match == match;

        loop invariant i_25: \forall integer j; j < m ==> match + j is valid memory address;

        loop invariant i_26: \forall integer j; 0 <= j < m ==> p[j] == t[match + j];

        loop invariant i_27: p == p;


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
