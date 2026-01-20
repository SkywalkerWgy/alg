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
        loop invariant i_29: i + j == 1;

        loop invariant i_30: 0 < i;

        loop invariant i_31: i % 2 == 1 || j % 2 == 0;

        loop invariant i_32: i + j + b == 2;

        loop invariant i_33: 0 < a;

        loop invariant i_34: b >= a;


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

        loop invariant i_35: i + j == 1;

        loop invariant i_36: 0 < i;

        loop invariant i_37: i % 2 == 1 || j % 2 == 0;

        loop invariant i_38: i + j + b == 2;

        loop invariant i_39: 0 < a;

        loop invariant i_40: b >= a;

        loop invariant i_41: a == b;


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