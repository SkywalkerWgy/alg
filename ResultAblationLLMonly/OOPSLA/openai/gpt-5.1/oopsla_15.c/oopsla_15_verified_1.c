#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * from Invgen test suite
 */
/*@
    requires n > 0;
    requires k > n;
*/
void oopsla_15(int n, int k) {

    int i, j;

    j = 0;
// Loop A
    /*@
    loop invariant i_0: 0 <= j <= n;

    loop invariant i_1: k + j > n;


    loop assigns k;
    loop assigns j;
    */
    while( j < n ) {
        j++;
        k--;
    } 

    //@ assert  a_1: k>=0;
}
