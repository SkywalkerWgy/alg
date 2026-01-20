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
        loop invariant i_0: n > 0;

        loop invariant i_1: 1 <= i <= n;

        loop invariant i_2: 0 <= j <= i - 1;

        loop invariant i_3: k >= i;

        loop invariant i_8: 0 <= j && j <= i - 1;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_4: n > 0;

            loop invariant i_5: 1 <= i <= n;

            loop invariant i_6: 0 <= j <= i;

            loop invariant i_7: k >= i;


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
