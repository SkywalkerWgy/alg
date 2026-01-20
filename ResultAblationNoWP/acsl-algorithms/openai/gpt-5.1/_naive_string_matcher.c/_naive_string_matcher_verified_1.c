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
        loop invariant i_0: \valid_read(t);

        loop invariant i_1: \valid_read(p);

        loop invariant i_2: \valid(t + (0..n - 1));

        loop invariant i_3: \valid(p + (0..m - 1));

        loop invariant i_4: \separated(&t[0..(n - 1)], &p[0..(m - 1)]);

        loop invariant i_5: n > 0;

        loop invariant i_6: m > 0;

        loop invariant i_7: n >= m;

        loop invariant i_8: 0 <= i && i <= n - m;


        loop assigns i;
    */
    for (int i = 0; i < n - m; i++){
        // Loop B
        /*@
            loop invariant i_9: \valid_read(t);

            loop invariant i_10: \valid_read(p);

            loop invariant i_11: \valid(t + (0..n - 1));

            loop invariant i_12: \valid(p + (0..m - 1));

            loop invariant i_13: \separated(&t[0..(n - 1)], &p[0..(m - 1)]);

            loop invariant i_14: n > 0;

            loop invariant i_15: m > 0;

            loop invariant i_16: n >= m;

            loop invariant i_17: 0 <= i && i <= n - m;

            loop invariant i_18: 0 <= j && j <= m;


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