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
    loop invariant i_0: j <= n;

    loop invariant i_1: k >= 0;

    loop invariant i_2: j < n && k >= 0;

    loop invariant i_3: k >= 0 && j >= 0;

    loop invariant i_4: k >= 0 && j >= 0 && j < n;

    loop invariant i_5: j >= 0 && k >= 0 && j < n;

    loop invariant i_6: j >= 0 && j < n && k >= 0;

    loop invariant i_7: j >= 0 && j < n;

    loop invariant i_8: j >= 0 && j < n && k >= 0 && j < n;

    loop invariant i_9: k >= 0 && j < n;

    loop invariant i_11: j < n;


    loop assigns k;
    loop assigns j;
    */
    while( j < n ) {
        j++;
        k--;
    } 

    //@ assert  a_1: k>=0;
}
