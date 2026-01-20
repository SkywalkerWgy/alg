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
        loop invariant i_0: k == i0;

        loop invariant i_1: n0 < 0 ==> i0 == 0;

        loop invariant i_2: n0 >= 0 ==> 0 <= i0 <= n0;


        loop assigns i0, k;
    */
    while( i0 < n0 ) {
        i0++;
        k++;
    }

    int i1 = 0;

    // Loop B
    /*@
        loop invariant i_3: n1 < 0 ==> i1 == 0;

        loop invariant i_4: n1 >= 0 ==> 0 <= i1 <= n1;

        loop invariant i_5: n0 < 0 ==> k - i1 == 0;

        loop invariant i_6: n0 >= 0 ==> k - i1 == n0;


        loop assigns i1, k;
    */
    while( i1 < n1 ) {
        i1++;
        k++;
    }

    int j1 = 0;

    // Loop C
    /*@
        loop invariant i_7: 0 <= j1;

        loop invariant i_8: n0 < 0 && n1 < 0 ==> k + j1 == 0;

        loop invariant i_9: n0 < 0 && n1 >= 0 ==> k + j1 == n1;

        loop invariant i_10: n0 >= 0 && n1 < 0 ==> k + j1 == n0;

        loop invariant i_11: n0 >= 0 && n1 >= 0 ==> k + j1 == n0 + n1;


        loop assigns j1, k;
    */
    while( j1 < n0 + n1 ) {
        //@ assert(k > 0);
        j1++;
        k--;
    }
}