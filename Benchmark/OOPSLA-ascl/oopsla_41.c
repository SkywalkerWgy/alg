#include <assert.h>
/*@
ensures \result >= 0;
*/
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires n > 0;
    ensures  e_1: z > 2 * n;
*/
void oopsla_41(int n, int i, int j, int z) {
    i = 0;
    j = 0;

    /*@
        loop assigns j, i;
    */
    while (i <= n) {
        i++;
        j += i;
    }

    z = i + j;
}
