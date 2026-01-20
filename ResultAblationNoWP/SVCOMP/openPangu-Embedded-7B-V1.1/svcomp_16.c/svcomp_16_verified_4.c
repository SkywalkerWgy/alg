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
        loop invariant i_54: k >= 2 * i;

        loop invariant i_55: k < n;

        loop invariant i_56: for svcomp_16 ``` loop invariant 1 <= i <= n;

        loop invariant i_57: 1 <= i <= n;

        loop invariant i_58: j >= 2 * i;

        loop invariant i_59: j < n;

        loop invariant i_60: j <= n - 1;

        loop invariant i_61: k >= j;

        loop invariant i_62: k <= n;

        loop invariant i_63: i + j + k <= 3 * n;

        loop invariant i_64: i == 0 && j == 0 && k == 0;

        loop invariant i_65: i < n;

        loop invariant i_66: i >= 0;

        loop invariant i_67: i <= n - 1;

        loop invariant i_68: j % 2 == 0;

        loop invariant i_69: k % 2 == 0;

        loop invariant i_70: i + j + k == n;

        loop invariant i_71: j >= 2 * i && j <= n - 1;

        loop invariant i_72: k >= 2 * i && k <= n;

        loop invariant i_73: k == j && k >= 2 * i;

        loop invariant i_74: j >= 2 * i && j < n;


        loop assigns i, j, k;
    */
    for (i = 0; i < n; i++) {
        // Loop B
        /*@
            loop invariant i_76: i >= 0 && i < n && j >= 2 * i && j < n && k >= 2 * i && k < n && i + j + k == n;


            loop assigns j, k;
        */
        for (j = 2 * i; j < n; j++) {

            if(unknown1()) {
                // Loop C
                /*@
                    loop invariant i_75: i >= 0 && i < n && j >= 2 * i && j < n && k >= 2 * i && k < n && i + j + k == n;


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