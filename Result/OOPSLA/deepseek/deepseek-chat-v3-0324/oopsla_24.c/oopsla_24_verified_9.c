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
        loop invariant i_2: \forall integer x; i <= x < n ==> x >= i;

        loop invariant i_3: \forall integer y; i <= y < n ==> y >= i;

        loop invariant i_4: \forall integer z; i <= z < n ==> z >= i;

        loop invariant i_12: n >= 0 ==> 0 <= i <= n;

        loop invariant i_15: i >= 0;

        loop invariant i_19: i >= 0 && (i == 0 || i > 0);

        loop invariant i_20: n >= 0 ==> i <= n;


        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        // Loop B
        /*@
            loop invariant i_6: i <= j <= n;

            loop invariant i_7: \forall integer k; j <= k < n ==> k >= i;

            loop invariant i_8: \forall integer x; i <= x < j ==> x >= i;


            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            // Loop C
            /*@
                loop invariant i_9: j <= k <= n;

                loop invariant i_10: \forall integer x; k <= x < n ==> x >= i;

                loop invariant i_13: k >= i;

                loop invariant i_14: \forall integer y; j <= y < k ==> y >= i;

                loop invariant i_16: k >= 0;

                loop invariant i_17: k >= j;

                loop invariant i_18: i <= k;


                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
