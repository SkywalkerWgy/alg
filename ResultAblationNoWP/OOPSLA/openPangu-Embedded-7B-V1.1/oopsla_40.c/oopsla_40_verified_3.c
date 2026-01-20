#include <assert.h>
int unknown1();
int unknown2();

/*@
requires flag > 0;
*/
void oopsla_40(int flag) {
    int i, j, k;
    j = 1;
    if (flag) {
        i = 0;
    } else {
        i = 1;
    }

    // Loop A
    /*@
        loop invariant i_20: && flag == 0 => i == 1 && j == 1;

        loop invariant i_21: flag == 0 => i == 1 && j == 1 && i % 2 == 1;

        loop invariant i_22: flag == 1 => i == 0 && j == 1;

        loop invariant i_23: 0 <= i <= 1 && 0 <= j <= 1;


        loop assigns j;
        loop assigns i;
    */
    while (unknown1()) {
        i += 2;
        if (i % 2 == 0) {
        j += 2;
        } else j++;
    }

    int a = 0;
    int b = 0;

    // Loop B
    /*@

        loop invariant i_24: flag == 0 => a == 0 && b == 0;

        loop invariant i_25: flag == 1 => a == 0 && b == 0 && a == b;

        loop invariant i_26: 0 <= a <= 1 && 0 <= b <= 1 && a == b;

        loop invariant i_27: \exists integer k; 0 <= k <= j && a == i[k];

        loop invariant i_28: \forall integer k; 0 <= k < j && a[k] == a;

        loop invariant i_29: \forall integer k; 0 <= k < j && a[k] == i[k];

        loop invariant i_30: \forall integer k; 0 <= k < j && i[k] == i;

        loop invariant i_31: b == 0;

        loop invariant i_32: flag == 0 => i == 1 && j == 1 && i % 2 == 1;

        loop invariant i_33: flag == 1 => i == 0 && j == 1;

        loop invariant i_34: 0 <= i <= 1 && 0 <= j <= 1;

        loop invariant i_35: flag == 0 => a == b == 0;

        loop invariant i_36: flag == 1 => a == b == 0;


        loop assigns j;
        loop assigns i;
        loop assigns b;
        loop assigns a;
    */
    while (unknown2()) {
        a++;
        b += (j - i);
    }


    //@ assert  a_1: flag ==> a == b;
    
}