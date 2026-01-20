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
        loop invariant i_1: k >= 0;


        loop assigns i0, k;
    */
    while( i0 < n0 ) {
        i0++;
        k++;
    }

    int i1 = 0;

    // Loop B
    /*@
        loop invariant i_8: k >= 0;


        loop assigns i1, k;
    */
    while( i1 < n1 ) {
        i1++;
        k++;
    }

    int j1 = 0;

    // Loop C
    /*@
        loop invariant i_5: k >= 0;


        loop assigns j1, k;
    */
    while( j1 < n0 + n1 ) {
        //@ assert(k > 0);
        j1++;
        k--;
    }
}