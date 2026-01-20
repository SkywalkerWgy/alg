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
        loop invariant i_20: 1 <= i <= n;

        loop invariant i_21: j == 0 || j == i;

        loop invariant i_22: k >= i;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_23: 0 <= j <= i;

            loop invariant i_24: k >= i + (j * (i - (j - 1) / 2));

            loop invariant i_25: \forall integer m; 0 <= m < j ==> k >= i + (m * (i - (m - 1) / 2));


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
