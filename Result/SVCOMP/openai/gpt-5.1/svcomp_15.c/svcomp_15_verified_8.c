# define INT_MAX 2147483647

int unknown1();

/*@
    requires l > 0;
    requires l < INT_MAX;
    requires n < INT_MAX;
*/
void svcomp_15(int n, int l) {
    int i, k;
    // Loop A
    /*@
        loop invariant i_0: 1 <= k;

        loop invariant i_1: l > 0;

        loop invariant i_2: n < INT_MAX;

        loop invariant i_3: l >= \at(l,Pre);

        loop invariant i_4: l <= \at(l,Pre) + (k - 1);

        loop invariant i_9: 0 < l;

        loop invariant i_10: n <= INT_MAX - 1;

        loop invariant i_11: l - \at(l,Pre) <= k - 1;

        loop invariant i_14: k >= 1;

        loop invariant i_15: l >= 1;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_5: l > 0;

            loop invariant i_7: n < INT_MAX;

            loop invariant i_8: 1 <= i;

            loop invariant i_12: 0 < l;

            loop invariant i_13: 0 < i;

            loop invariant i_16: i >= l;

            loop invariant i_17: l >= 1;

            loop invariant i_18: 1 <= l;

            loop invariant i_19: i >= 1;

            loop invariant i_20: n <= INT_MAX - 1;


            loop assigns i;
        */
        for (i = l; i < n; i++){  
            //@ assert 1 <= i;
        }
        if(unknown1()) {
            l = l + 1;
        }
    }
}