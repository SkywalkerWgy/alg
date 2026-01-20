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
        loop invariant i_10: i + j == 1;

        loop invariant i_11: flag == 0 => i == 0;

        loop invariant i_12: \forall j; i >= j;

        loop invariant i_13: a == b || flag == 0;

        loop invariant i_14: b >= a;

        loop invariant i_15: \forall integer k; a <= k < b || flag == 0;


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

        loop invariant i_16: i + j == 1;

        loop invariant i_17: flag == 0 => i == 0;

        loop invariant i_18: i >= j;

        loop invariant i_19: b >= a;

        loop invariant i_20: \forall integer k; a <= k < b || flag == 0;

        loop invariant i_21: a + (j - i) == b;

        loop invariant i_22: i == 0 || flag == 0;

        loop invariant i_23: a == b && flag == 0;

        loop invariant i_24: \forall integer k; \ni == 0 || flag == 0;

        loop invariant i_25: \forall integer k; \ni == 1 || flag == 0;

        loop invariant i_26: \forall integer k; a == b && flag == 0;

        loop invariant i_27: \forall integer k; a <= b && flag == 0;

        loop invariant i_28: a <= b && flag == 0;


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