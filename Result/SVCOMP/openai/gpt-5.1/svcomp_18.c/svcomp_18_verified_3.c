# define INT_MAX 2147483647
# define INT_MIN -2147483648

/*@
    requires INT_MIN < n0 && n0 < INT_MAX;
    requires INT_MIN < n1 && n1 < INT_MAX;
*/
void svcomp_18(int n0, int n1) {
    int i0 = 0;
    int k = 0;

    // Loop A
    /*@
        loop invariant i_0: INT_MIN < n0 && n0 < INT_MAX;

        loop invariant i_1: INT_MIN < n1 && n1 < INT_MAX;

        loop invariant i_2: 0 <= i0;

        loop invariant i_3: 0 <= k;

        loop invariant i_4: i0 == k;

        loop invariant i_5: i0 <= n0;

        loop invariant i_18: n0 <= 0 || i0 <= n0;

        loop invariant i_24: n0 >= 0 ==> i0 <= n0;


        loop assigns i0, k;
    */
    while( i0 < n0 ) {
        i0++;
        k++;
    }

    int i1 = 0;

    // Loop B
    /*@
        loop invariant i_6: INT_MIN < n0 && n0 < INT_MAX;

        loop invariant i_7: INT_MIN < n1 && n1 < INT_MAX;

        loop invariant i_8: 0 <= i1;

        loop invariant i_9: 0 <= k;

        loop invariant i_10: i1 <= n1;

        loop invariant i_11: k == n0 + i1;

        loop invariant i_19: n1 <= 0 || i1 <= n1;

        loop invariant i_20: n0 > INT_MIN && n0 < INT_MAX;

        loop invariant i_21: n1 > INT_MIN && n1 < INT_MAX;

        loop invariant i_22: i1 >= 0;

        loop invariant i_23: k >= 0;


        loop assigns i1, k;
    */
    while( i1 < n1 ) {
        i1++;
        k++;
    }

    int j1 = 0;

    // Loop C
    /*@
        loop invariant i_12: INT_MIN < n0 && n0 < INT_MAX;

        loop invariant i_13: INT_MIN < n1 && n1 < INT_MAX;

        loop invariant i_14: 0 <= j1;

        loop invariant i_15: 0 <= k;

        loop invariant i_16: j1 <= n0 + n1;

        loop invariant i_17: k == n0 + n1 - j1;


        loop assigns j1, k;
    */
    while( j1 < n0 + n1 ) {
        //@ assert(k > 0);
        j1++;
        k--;
    }
}