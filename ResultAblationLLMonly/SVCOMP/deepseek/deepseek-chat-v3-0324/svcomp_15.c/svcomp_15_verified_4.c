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
        loop invariant i_0: 1 <= k <= n;

        loop invariant i_1: l <= n;

        loop invariant i_2: l >= \at(l, Pre);

        loop invariant i_6: k <= l ==> l == \at(l, Pre);

        loop invariant i_7: s for Loop A: ``` loop invariant 1 <= k <= n;

        loop invariant i_8: \at(l, Pre) <= l <= n;

        loop invariant i_9: k > l ==> l == \at(l, Pre) + (k - \at(l, Pre));

        loop invariant i_10: \forall integer j; \at(l, Pre) <= j < l ==> unknown1() was true at iteration j;


        loop assigns i, k, l;
    */
    for (k = 1; k < n; k++){
        // Loop B
        /*@
            loop invariant i_3: l <= i <= n;

            loop invariant i_4: \at(l, Pre) <= l;

            loop invariant i_5: 1 <= k <= n;

            loop invariant i_11: \forall integer j; l <= j < i ==> unknown1() was true at iteration j;

            loop invariant i_12: i == l || i > l ==> l == \at(l, Pre) + (k - \at(l, Pre));

            loop invariant i_13: s for Loop B: ``` loop invariant i_3: l <= i <= n;


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