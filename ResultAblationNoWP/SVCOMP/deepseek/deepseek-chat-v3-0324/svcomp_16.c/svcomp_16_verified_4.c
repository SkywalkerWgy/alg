# define INT_MAX 2147483647

int unknown1();

/*@
    requires n < INT_MAX;
*/
int svcomp_16(int k, int n) {
    int i, j;

    if(k == n) {
    }
    else {
        goto END;
    }
    // Loop A
    /*@
        loop invariant i_27: 0 <= i <= n;

        loop invariant i_28: k == n;

        loop invariant i_29: \forall integer x; 0 <= x < i ==> \forall integer y; 2*x <= y < n ==> (unknown1() ==> (\forall integer z; y <= z < n ==> z >= 2*x)) && (!unknown1() ==> (k >= n && k <= n)); ```;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_32: 2*i <= j <= n;

            loop invariant i_33: k == n;

            loop invariant i_34: \forall integer x; 0 <= x < i ==> \forall integer y; 2*x <= y < n ==> (unknown1() ==> (\forall integer z; y <= z < n ==> z >= 2*x)) && (!unknown1() ==> (k >= n && k <= n)); ```;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_30: j <= k <= n;

                    loop invariant i_31: \forall integer z; j <= z < k ==> z >= 2*i;


                    loop assigns k;
                */
                for (k = j; k < n; k++) {
                    //@ assert(k >= 2*i);
                }
            }
            else {
                //@ assert( k >= n );
                //@ assert( k <= n );
            }
        }
    }

END:
    return 0;
}