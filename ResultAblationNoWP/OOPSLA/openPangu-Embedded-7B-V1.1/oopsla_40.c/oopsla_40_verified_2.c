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
        loop invariant i_6: flag == 0 || i == 0;

        loop invariant i_7: j == 1;

        loop invariant i_8: i <= 1;

        loop invariant i_9: a == 0 || b == 0;

        loop invariant i_10: j - i >= 0 && (a == 0 && b == j - i) || (a == 1 && b == 0);

        loop invariant i_11: \forall int k in [0, j-1]; (k == 0 && a == 0) || (k == j-1 && a == 1);

        loop invariant i_12: b % 2 == (j - i) % 2;

        loop invariant i_13: \forall int k; 0 <= k < j;

        loop invariant i_14: \exists int k; 0 <= k < j && (a == 0 && b == j - k) || (a == 1 && b == j - k);


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

        loop invariant i_15: a >= 0 && b >= 0;

        loop invariant i_16: b - a >= (j - i) % 2;

        loop invariant i_17: j >= i;

        loop invariant i_18: i < unknown2();

        loop invariant i_19: \exists int k; 0 <= k < j && (a == 0 && b == j - k) || (a == 1 && b == j - k);


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