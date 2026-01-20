#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires k == 1;
    requires i == 1;
    requires j == 0;
    ensures e_1: k >= n;
*/
void oopsla_17(int n, int i, int j, int k){
    /*@
        loop assigns i, j, k;
    */
    while(i < n) {
        j = 0;

        /*@
            loop assigns j, k;
        */
        while(j < i) {
            k += (i-j);
            j++;
        }
        i++;
    }
}
