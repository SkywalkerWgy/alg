#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires k >= 0;
    requires i == 0;
    requires j == 0;
    ensures  e_1: flag == 1 ==> j == i;
*/
void oopsla_44(int k, int flag, int i, int j, int n) {
    if (flag == 1){
        n = 1;
    } else {
        n = 2;
    }

    /*@
        loop assigns j, i;
    */
    while (i <= k) {
        i++;
        j = j + n;
    }
}
