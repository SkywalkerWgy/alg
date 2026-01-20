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
    
    /*@
        loop assigns i,j,k;
    */
    for (i=0;i<n;i++){

        /*@
            loop assigns j,k;
        */
        for (j=i;j<n;j++){

            /*@
                loop assigns k;
            */
            for (k=j;k<n;k++){
                //@ assert  a_1: k>=i;
            }
        }
    }
}
