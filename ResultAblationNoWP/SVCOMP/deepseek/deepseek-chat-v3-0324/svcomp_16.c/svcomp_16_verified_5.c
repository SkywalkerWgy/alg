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
        loop invariant i_35: 0 <= i <= n;

        loop invariant i_36: \forall integer t; 0 <= t < i ==> \at(k, Pre) == n;

        loop invariant i_37: k >= n;

        loop invariant i_38: \forall integer t; 0 <= t < i ==> \forall integer p; 2*t <= p < n ==> k >= p;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_41: 2*i <= j <= n;

            loop invariant i_42: k >= n;

            loop invariant i_43: \forall integer t; 0 <= t < i ==> \at(k, Pre) == n;

            loop invariant i_44: \forall integer t; 0 <= t < i ==> \forall integer p; 2*t <= p < n ==> k >= p;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_39: j <= k <= n;

                    loop invariant i_40: \forall integer p; j <= p < k ==> p >= 2*i;


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