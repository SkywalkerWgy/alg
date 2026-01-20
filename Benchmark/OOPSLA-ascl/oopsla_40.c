#include <assert.h>
int unknown1();
int unknown2();

/*@
    requires flag > 0;
    ensures  e_1: flag ==> a == b;
*/
void oopsla_40(int flag, int i, int j, int k, int a, int b) {
    
    j = 1;
    if (flag) {
        i = 0;
    } else {
        i = 1;
    }

    /*@
        loop assigns j, i;
    */
    while (unknown1()) {
        i += 2;
        if (i % 2 == 0) {
            j += 2;
        } else {
            j++;
        }
    }

    a = 0;
    b = 0;

    /*@
        loop assigns b, a;
    */
    while (unknown2()) {
        a++;
        b += (j - i);
    }
}
