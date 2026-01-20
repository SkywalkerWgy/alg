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
        loop invariant i_4: i <= n;

        loop invariant i_5: j >= 0;

        loop invariant i_6: k >= 0;

        loop invariant i_7: (i - j) == k;

        loop invariant i_8: i < n && j <= i;

        loop invariant i_9: j == i - k;

        loop invariant i_10: k < i;

        loop invariant i_11: i < n && j >= 0;

        loop invariant i_12: k >= 0 && j >= 0;

        loop invariant i_13: k <= i - 1;

        loop invariant i_14: (i - j) == k && k < i;

        loop invariant i_15: k >= j;

        loop invariant i_16: j < i;

        loop invariant i_17: j <= i - 1;

        loop invariant i_18: k + j <= i;

        loop invariant i_19: k + j <= i - 1;

        loop invariant i_20: i >= 1 && n >= 1;

        loop invariant i_21: k == 1;

        loop invariant i_22: i == 1 && n == 1;

        loop invariant i_23: k < n;

        loop invariant i_24: j == 0 && k == 1 && i == 1;

        loop invariant i_25: k == i;

        loop invariant i_26: i == j + k && k >= 0 && j >= 0;

        loop invariant i_27: j >= 0 && k >= 0;

        loop invariant i_28: i >= 1;

        loop invariant i_29: n >= 1;

        loop invariant i_30: i - j == k;

        loop invariant i_31: i - j == k && k >= 0 && j >= 0;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_32: i >= 1 && n >= 1;

            loop invariant i_33: k == 1;

            loop invariant i_34: j == 0 && i == 1 && n == 1;

            loop invariant i_35: k >= 0 && j >= 0;

            loop invariant i_36: (i - j) == k;

            loop invariant i_37: k < i;

            loop invariant i_38: i < n && j <= i;

            loop invariant i_39: k + j <= i;

            loop invariant i_40: k + j <= i - 1;

            loop invariant i_41: i == j + k && k >= 0 && j >= 0;

            loop invariant i_42: j >= 0 && k >= 0;

            loop invariant i_43: i >= 1;

            loop invariant i_44: n >= 1;

            loop invariant i_45: i - j == k;

            loop invariant i_46: k >= j;

            loop invariant i_47: j < i;

            loop invariant i_48: j <= i - 1;


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
