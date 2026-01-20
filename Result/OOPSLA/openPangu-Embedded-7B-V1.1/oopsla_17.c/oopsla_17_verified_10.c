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
        loop invariant i_0: i <= n;

        loop invariant i_1: j <= i;

        loop invariant i_11: k >= (i - j);

        loop invariant i_12: j >= 0;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_4: i <= n;

            loop invariant i_5: k >= (i - j);

            loop invariant i_6: k >= (n - i);

            loop invariant i_7: j <= i;

            loop invariant i_8: j >= 0;

            loop invariant i_13: k <= n - i;


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
