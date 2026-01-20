#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * "nested5.c" from InvGen test suite
 */

void oopsla_24() {
    int i,j,k,n;
    
    // Loop A
    /*@
        loop invariant i_89: 0 <= i <= n;

        loop invariant i_90: 0 <= j <= n;

        loop invariant i_91: 0 <= k <= n;

        loop invariant i_92: i <= j;

        loop invariant i_93: i <= j <= n;

        loop invariant i_94: j <= k;

        loop invariant i_95: j <= k <= n;

        loop invariant i_96: k >= i;

        loop invariant i_97: k >= i && k <= n;

        loop invariant i_100: i <= k;

        loop invariant i_101: j <= n;

        loop invariant i_102: k >= i || k == j;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_99: j >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_98: k >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
