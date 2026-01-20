#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

/*@
    requires n == 10;
    requires \valid(p + (0..(n)));
    requires \valid(m + (0..(n)));
    requires \valid(m[0..(n)] + (0..(n)));
    requires \forall integer i, j; 0 <= i < n && 0 <= j < n && i != j ==> \separated(&m[i] + (0..(n)), &m[j] + (0..(n)), &p[0..(n)]);
    requires \separated(&m[0..(n)] + (0..(n)), &p[0..(n)]);
    requires \forall integer k; 0 <= k <= n ==> 0 < p[k] < 5;
    requires \forall integer r; 0 <= r <= n ==> m[r][r] == 0;
    requires \forall integer i, j; 0 <= i <= n  && 0 <= j <= n && i != j ==> m[i][j] == 2147483647;
    ensures e_1: \forall integer j; 2 <= j <= n ==>
                (\forall integer g; 1 <= g <= n - j + 1 ==> 
                    (\forall integer h; g <= h < g + j - 1 ==> 
                        m[g][g + j - 1] <= m[g][h] + m[h + 1][g + j - 1] + p[g - 1] * p[h] * p[g + j - 1]));
    assigns m[1..(n)][1..(n)];
*/
int _matrix_chain(int p[], int** m, int n) {

    // Loop A
    /*@
        loop invariant i_9: s for Loop A: ``` loop invariant 2 <= l <= n + 1;

        loop invariant i_10: 2 <= l <= n + 1;

        loop invariant i_11: \forall integer j; 2 <= j < l ==> (\forall integer g; 1 <= g <= n - j + 1 ==> (\forall integer h; g <= h < g + j - 1 ==> m[g][g + j - 1] <= m[g][h] + m[h + 1][g + j - 1] + p[g - 1] * p[h] * p[g + j - 1])); loop invariant \forall integer i, j; 1 <= i <= n && 1 <= j <= n && (j - i + 1 >= l || j < i) ==> m[i][j] == \at(m[i][j], Pre); ```;

        loop invariant i_12: \forall integer i, j; 1 <= i <= n && 1 <= j <= n && (j - i + 1 >= l || j < i) ==> m[i][j] == \at(m[i][j], Pre);


        loop assigns l;
        loop assigns m[1..(n)][1..(n)];
    */
    for (int l = 2; l <= n; l++) {
        // Loop B
        /*@
            loop invariant i_16: 1 <= i <= n - l + 2;

            loop invariant i_17: \forall integer j; 1 <= j < i ==> (\forall integer k; j <= k < j + l - 1 ==> m[j][j + l - 1] <= m[j][k] + m[k + 1][j + l - 1] + p[j - 1] * p[k] * p[j + l - 1]); loop invariant \forall integer a, b; 1 <= a <= n && 1 <= b <= n && (b - a + 1 > l || a > b || (a >= i && b == a + l - 1)) ==> m[a][b] == \at(m[a][b], Pre);

            loop invariant i_18: \forall integer a, b; 1 <= a <= n && 1 <= b <= n && (b - a + 1 > l || a > b || (a >= i && b == a + l - 1)) ==> m[a][b] == \at(m[a][b], Pre);


            loop assigns m[1..(n)][1..(n)];
            loop assigns i;
        */
        for (int i = 1; i <= n - l + 1; i++) {
            int end = i + l - 1;
            m[i][end] = 2147483647;
            // Loop C
            /*@
                loop invariant i_13: i <= k <= end;

                loop invariant i_14: m[i][end] == 2147483647 || (\exists integer h; i <= h < k && m[i][end] == m[i][h] + m[h + 1][end] + p[i - 1] * p[h] * p[end]); loop invariant \forall integer h; i <= h < k ==> m[i][end] <= m[i][h] + m[h + 1][end] + p[i - 1] * p[h] * p[end];

                loop invariant i_15: \forall integer h; i <= h < k ==> m[i][end] <= m[i][h] + m[h + 1][end] + p[i - 1] * p[h] * p[end];


                loop assigns m[i][end];
                loop assigns k;
            */
            for (int k = i; k < end; k++) {
                int q = m[i][k] + m[k + 1][end] + p[i - 1] * p[k] * p[end];
                if (q < m[i][end]) {
                    m[i][end] = m[i][k] + m[k + 1][end] + p[i - 1] * p[k] * p[end];
                }
            }
            
        }
    }
    return m[1][n];
}



 