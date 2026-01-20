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
        loop invariant i_15: i <= n && j >= 0;

        loop invariant i_16: j <= i && k >= 0;

        loop invariant i_17: i <= n;

        loop invariant i_18: j >= 0;

        loop invariant i_19: k >= 0;


        loop assigns i, j;
    */
    while(i < n) {
        j = 0;

        // Loop B
        /*@
            loop invariant i_20: j <= i && k >= 0;

            loop invariant i_21: i <= n && j >= 0;

            loop invariant i_22: k >= 0 && i - j <= k;


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
