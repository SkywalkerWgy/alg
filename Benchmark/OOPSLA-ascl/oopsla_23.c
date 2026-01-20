#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * ex49 from NECLA Static Analysis Benchmarks
 */

/*@
    requires n >= 0;
    requires sum == 0;
    ensures e_1: sum >= 0;
*/
void oopsla_23(int n, int sum) {
    int i;

    /*@
        loop assigns sum;
        loop assigns i;
    */
    for (i = 0; i < n; ++i){
        sum = sum + i;
    }
}