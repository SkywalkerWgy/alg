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
        loop invariant i_23: i <= n;

        loop invariant i_24: j >= 0 && j < i;

        loop invariant i_25: k >= 0 && k <= i;

        loop invariant i_26: k >= i - j;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_27: j >= 0 && j < i;

            loop invariant i_28: i >= 1;

            loop invariant i_29: k >= i - j;

            loop invariant i_30: k <= i;


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
