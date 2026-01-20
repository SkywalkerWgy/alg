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

        loop invariant i_4: 0 <= i && i <= n - m;


        loop assigns i;
    */
    for (int i = 0; i < n - m; i++){
        // Loop B
        /*@
            loop invariant i_2: 0 <= j <= m;

            loop invariant i_3: \forall integer k; 0 <= k < j ==> !string_same(t, p, n, m, k);

            loop invariant i_5: \forall integer k; 0 <= k < i ==> !string_same(t, p, n, m, k);


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