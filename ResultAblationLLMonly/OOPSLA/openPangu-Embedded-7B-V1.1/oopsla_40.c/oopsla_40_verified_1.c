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
        loop invariant i_0: flag == 0 || i == 0;

        loop invariant i_1: j == 1;

        loop invariant i_2: i + j == 1;

        loop invariant i_3: a == 0 || b == 0;

        loop invariant i_4: b == a;


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

        loop invariant i_5: flag == 0 || i == 0;

        loop invariant i_6: j == 1;

        loop invariant i_7: i + j == 1;

        loop invariant i_8: a == 0 || b == 0;

        loop invariant i_9: b == a;


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