#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires x == 0;
    requires y == 0;
    requires i == 0;
    requires j == 0;
    ensures  e_1: j >= i;
*/
void oopsla_05(int flag, int x, int y, int i, int j){

    /*@
        loop assigns y;
        loop assigns x;
        loop assigns j;
        loop assigns i;
    */
    while(unknown1()) {
        x++;
        y++;
        i += x;
        j += y;
        if (flag){
            j += 1;
        }
    } 
}
