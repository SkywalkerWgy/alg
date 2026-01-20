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
        loop invariant i_48: 0 <= i;

        loop invariant i_49: 0 <= j;

        loop invariant i_50: j <= 1;

        loop invariant i_51: (flag == 0 => i == 1) && (flag == 1 => i == 0);

        loop invariant i_52: 0 <= a;

        loop invariant i_53: 0 <= b;

        loop invariant i_54: b == a + (j - i);

        loop invariant i_55: flag == oopsla_40;


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

        loop invariant i_56: 0 <= a;

        loop invariant i_57: 0 <= b;

        loop invariant i_58: b == a + (j - i);

        loop invariant i_59: a <= b;


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