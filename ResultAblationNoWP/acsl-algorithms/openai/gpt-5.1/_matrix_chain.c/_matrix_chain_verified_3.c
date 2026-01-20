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
        loop invariant i_0: n == 10;

        loop invariant i_1: \valid(p + (0..(n)));

        loop invariant i_2: \valid(m + (0..(n)));

        loop invariant i_3: \valid(m[0..(n)] + (0..(n)));

        loop invariant i_4: \forall integer i, j; 0 <= i < n && 0 <= j < n && i != j ==> \separated(&m[i] + (0..(n)), &m[j] + (0..(n)), &p[0..(n)]);

        loop invariant i_5: \separated(&m[0..(n)] + (0..(n)), &p[0..(n)]);

        loop invariant i_6: \forall integer k; 0 <= k <= n ==> 0 < p[k] < 5;

        loop invariant i_7: \forall integer r; 0 <= r <= n ==> m[r][r] == 0;

        loop invariant i_8: 2 <= l <= n + 1;

        loop invariant i_9: \forall integer j; 2 <= j < l ==> (\forall integer g; 1 <= g <= n - j + 1 ==> (\forall integer h; g <= h < g + j - 1 ==> m[g][g + j - 1] <= m[g][h] + m[h + 1][g + j - 1] + p[g - 1] * p[h] * p[g + j - 1]));;

        loop invariant i_37: \valid(p + (0..n));

        loop invariant i_38: \valid(m + (0..n));

        loop invariant i_39: \valid(m[0..n] + (0..n));

        loop invariant i_40: \forall integer i, j; 0 <= i < n && 0 <= j < n && i != j ==> \separated(&m[i] + (0..n), &m[j] + (0..n), &p[0..n]);

        loop invariant i_41: \separated(&m[0..n] + (0..n), &p[0..n]);


        loop assigns l;
        loop assigns m[1..(n)][1..(n)];
    */
    for (int l = 2; l <= n; l++) {
        // Loop B
        /*@
            loop invariant i_12: n == 10;

            loop invariant i_13: \valid(p + (0..(n)));

            loop invariant i_14: \valid(m + (0..(n)));

            loop invariant i_15: \valid(m[0..(n)] + (0..(n)));

            loop invariant i_16: \forall integer a, b; 0 <= a < n && 0 <= b < n && a != b ==> \separated(&m[a] + (0..(n)), &m[b] + (0..(n)), &p[0..(n)]);

            loop invariant i_17: \separated(&m[0..(n)] + (0..(n)), &p[0..(n)]);

            loop invariant i_18: \forall integer k; 0 <= k <= n ==> 0 < p[k] < 5;

            loop invariant i_19: \forall integer r; 0 <= r <= n ==> m[r][r] == 0;

            loop invariant i_20: 2 <= l <= n + 1;

            loop invariant i_21: \forall integer j; 2 <= j < l ==> (\forall integer g; 1 <= g <= n - j + 1 ==> (\forall integer h; g <= h < g + j - 1 ==> m[g][g + j - 1] <= m[g][h] + m[h + 1][g + j - 1] + p[g - 1] * p[h] * p[g + j - 1])); loop invariant 1 <= i <= n - l + 2; loop invariant \forall integer g; 1 <= g < i ==> (\forall integer h; g <= h < g + l - 1 ==> m[g][g + l - 1] <= m[g][h] + m[h + 1][g + l - 1] + p[g - 1] * p[h] * p[g + l - 1]);;

            loop invariant i_22: 1 <= i <= n - l + 2;

            loop invariant i_23: \forall integer g; 1 <= g < i ==> (\forall integer h; g <= h < g + l - 1 ==> m[g][g + l - 1] <= m[g][h] + m[h + 1][g + l - 1] + p[g - 1] * p[h] * p[g + l - 1]);;


            loop assigns m[1..(n)][1..(n)];
            loop assigns i;
        */
        for (int i = 1; i <= n - l + 1; i++) {
            int end = i + l - 1;
            m[i][end] = 2147483647;
            // Loop C
            /*@
                loop invariant i_10: i <= k <= end;

                loop invariant i_11: \forall integer h; i <= h < k ==> m[i][end] <= m[i][h] + m[h + 1][end] + p[i - 1] * p[h] * p[end];

                loop invariant i_24: n == 10;

                loop invariant i_25: \valid(p + (0..(n)));

                loop invariant i_26: \valid(m + (0..(n)));

                loop invariant i_27: \valid(m[0..(n)] + (0..(n)));

                loop invariant i_28: \forall integer a, b; 0 <= a < n && 0 <= b < n && a != b ==> \separated(&m[a] + (0..(n)), &m[b] + (0..(n)), &p[0..(n)]);

                loop invariant i_29: \separated(&m[0..(n)] + (0..(n)), &p[0..(n)]);

                loop invariant i_30: \forall integer t; 0 <= t <= n ==> 0 < p[t] < 5;

                loop invariant i_31: \forall integer r; 0 <= r <= n ==> m[r][r] == 0;

                loop invariant i_32: 2 <= l <= n + 1;

                loop invariant i_33: 1 <= i <= n - l + 2;

                loop invariant i_34: 1 <= i < end && end <= n;

                loop invariant i_35: \forall integer j; 2 <= j < l ==> (\forall integer g; 1 <= g <= n - j + 1 ==> (\forall integer h; g <= h < g + j - 1 ==> m[g][g + j - 1] <= m[g][h] + m[h + 1][g + j - 1] + p[g - 1] * p[h] * p[g + j - 1])); loop invariant \forall integer g; 1 <= g < i ==> (\forall integer h; g <= h < g + l - 1 ==> m[g][g + l - 1] <= m[g][h] + m[h + 1][g + l - 1] + p[g - 1] * p[h] * p[g + l - 1]); loop invariant i <= k <= end; loop invariant \forall integer h; i <= h < k ==> m[i][end] <= m[i][h] + m[h + 1][end] + p[i - 1] * p[h] * p[end];

                loop invariant i_36: \forall integer g; 1 <= g < i ==> (\forall integer h; g <= h < g + l - 1 ==> m[g][g + l - 1] <= m[g][h] + m[h + 1][g + l - 1] + p[g - 1] * p[h] * p[g + l - 1]); loop invariant i <= k <= end;


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



 