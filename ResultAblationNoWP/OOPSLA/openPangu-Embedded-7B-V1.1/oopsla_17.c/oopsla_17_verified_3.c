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
        loop invariant i_49: k >= i;

        loop invariant i_50: i < n;

        loop invariant i_51: j >= 0;

        loop invariant i_52: j < i;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_53: k >= i;

            loop invariant i_54: i < n;

            loop invariant i_55: j >= 0;

            loop invariant i_56: j < i;


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
