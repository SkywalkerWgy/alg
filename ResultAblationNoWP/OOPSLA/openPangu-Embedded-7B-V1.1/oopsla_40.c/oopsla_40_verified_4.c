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
        loop invariant i_37: flag > 0 && 0 <= i <= 1;

        loop invariant i_38: a == 0 && b == (j - i);


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

        loop invariant i_39: flag > 0 && 0 <= i <= 1;

        loop invariant i_40: a == 0 && b == (j - i);

        loop invariant i_41: flag > 0 || i == 1;

        loop invariant i_42: \forall int k; 0 <= k < i <= 1 ==> k == i - 1;

        loop invariant i_43: \exists int k; 0 <= k < i && k == i - 1;

        loop invariant i_44: j % 2 == 1 || flag == 0;

        loop invariant i_45: b % 2 == 1;

        loop invariant i_46: a + b == j;

        loop invariant i_47: flag == 1 && 0 <= i <= 1;


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