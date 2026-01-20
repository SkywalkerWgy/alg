#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires n > 0;
*/
void oopsla_17(int n){
    int k=1;
    int i=1;
    int j=0;
    
    // Loop A
    /*@
        loop invariant i_57: 1 <= i <= n;

        loop invariant i_58: j <= i;

        loop invariant i_59: k >= 0;

        loop invariant i_60: j == i - i;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_61: 1 <= k <= i;

            loop invariant i_62: j <= i;

            loop invariant i_63: k >= 0;

            loop invariant i_64: j == i - j;

            loop invariant i_65: 1 <= i <= n;


            loop assigns k, j;
        */
        while(j < i) {
            k += (i-j);
            j++;
        }
        i++;
    }

    //@ assert a_1: (k >= n);
}
