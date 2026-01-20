#include <assert.h>

int unknown1();
int unknown2();

/*@
    requires t == 0;
    requires s == 0;
    requires a == 0;
    requires b == 0;
    ensures e_1: y <= 4;
*/
void oopsla_12(int flag, int t, int s, int a, int b, int x, int y){

    /*@
        loop assigns t, s, b, a;
    */
    while (unknown1()) {
        a++;
        b++;
        s += a;
        t += b;
        if (flag) {
            t += a;
        }
    } 

    x = 1;
    if (flag) {
        x = t - 2 * s + 2;
    }
    y = 0;

    /*@
        loop assigns y;
    */
    while (y <= x) {
        if (unknown2()) {
            y++;
        }
        else { 
            y += 2;
        }
    }
}
