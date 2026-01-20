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
        loop invariant i_1: l >= \at(l, Pre) && l <= \at(l, Pre) + k - 1;

        loop invariant i_6: k >= 1;

        loop invariant i_14: l >= 1;

        loop invariant i_15: 1 <= k;

        loop invariant i_18: l >= \at(l, Pre);

        loop invariant i_20: k >= 1 ==> k <= n + 1;

        loop invariant i_21: k == 1 ==> l == \at(l, Pre);

        loop invariant i_22: k > 1 ==> l >= \at(l, Pre) && l <= \at(l, Pre) + k - 1;

        loop invariant i_23: k <= n + 1 || n <= 0;

        loop invariant i_24: k >= 1 ==> k <= n + 1 || n <= 0;

        loop invariant i_25: l >= \at(l, Pre) && (k == 1 ? l == \at(l, Pre) : l <= \at(l, Pre) + k - 1);


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_4: \forall integer j; l <= j < i ==> j >= 1;

            loop invariant i_5: i == l ==> \at(i, LoopEntry) == l;

            loop invariant i_12: i >= l;


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