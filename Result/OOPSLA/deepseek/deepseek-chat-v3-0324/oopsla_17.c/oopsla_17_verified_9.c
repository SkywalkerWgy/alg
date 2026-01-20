#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires n > 0;
*/
void oopsla_17(int n){
    int k=1;
    int i=1;
    int j=0;
    
    // Loop A
    /*@
        loop invariant i_0: 1 <= i <= n;

        loop invariant i_1: j == 0;

        loop invariant i_2: k >= 1;

        loop invariant i_16: k == 1;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_3: j >= 0 && j <= i;

            loop invariant i_4: k >= 1 + (j * (i - (j - 1) / 2));

            loop invariant i_5: \forall integer m; 0 <= m < j ==> k >= 1 + (m * (i - (m - 1) / 2));

            loop invariant i_6: k >= 1;

            loop invariant i_7: \forall integer m; 0 <= m < j ==> k >= 1;

            loop invariant i_8: i >= 1;

            loop invariant i_9: \forall integer m; 0 <= m <= j ==> k == 1 + (m * (i - (m - 1) / 2));

            loop invariant i_10: k == 1 + (j * (i - (j - 1) / 2));

            loop invariant i_11: \forall integer m; 0 <= m < j ==> k == 1 + (m * (i - (m - 1) / 2)) + (i - m);

            loop invariant i_12: k == 1 + (j * (i - (j - 1) / 2)) + (i - j);

            loop invariant i_13: k >= 1 + (i * (i + 1) / 2);

            loop invariant i_14: \forall integer m; 0 <= m <= j ==> k == 1 + (m * (i - (m - 1) / 2)) + (i - m);

            loop invariant i_15: \forall integer m; 0 <= m <= i ==> 1 + (m * (i - (m - 1) / 2)) >= 1 + m;

            loop invariant i_17: j <= i;

            loop invariant i_19: k >= 1 + j;

            loop invariant i_20: \forall integer m; 0 <= m <= j ==> k >= 1 + m;

            loop invariant i_21: \forall integer m; j <= m <= i ==> k >= 1 + (m * (i - (m - 1) / 2));

            loop invariant i_24: k >= i + 1;

            loop invariant i_25: \forall integer m; 1 <= m <= i ==> k >= m + 1;

            loop invariant i_26: k >= 1 + i * (i + 1) / 2;

            loop invariant i_29: k >= i;

            loop invariant i_30: \forall integer m; 1 <= m <= n ==> k >= m;

            loop invariant i_32: \forall integer m; 0 <= m <= i ==> k >= 1 + m;

            loop invariant i_33: k >= 1 + i;

            loop invariant i_34: \forall integer m; 1 <= m <= i ==> k >= m;


            loop assigns k, j;
        */
        while(j < i) {
            k += (i-j);
            j++;
        }
        i++;
    }

    //@ assert a_1: (k >= n);
}
