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
    loop invariant i_5: j <= n;

    loop invariant i_6: k >= 0;


    loop assigns k;
    loop assigns j;
    */
    while( j < n ) {
        j++;
        k--;
    } 

    //@ assert  a_1: k>=0;
}
