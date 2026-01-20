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
        loop invariant i_0: 0 <= i;

        loop invariant i_1: i <= n;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_2: 0 <= i;

            loop invariant i_3: i <= n;

            loop invariant i_4: i <= j;

            loop invariant i_5: j <= n;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_6: 0 <= i;

                loop invariant i_7: i <= n;

                loop invariant i_8: i <= j;

                loop invariant i_9: j <= n;

                loop invariant i_10: j <= k;

                loop invariant i_11: k <= n;

                loop invariant i_12: k >= i;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
