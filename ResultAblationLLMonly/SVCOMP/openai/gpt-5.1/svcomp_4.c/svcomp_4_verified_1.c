// bhmr2007_true-unreach-call.c
// Source: Dirk Beyer, Thomas A. Henzinger, Rupak Majumdar, Andrey
// Rybalchenko: "Path Invariants", PLDI 2007.
int unknown1();

/*@ 
    requires 0 <= n && n < 1000000;
*/
int svcomp_4(int n, int i, int a, int b) {
    i = 0; a = 0; b = 0;
    
    // Loop A
    /*@
        loop invariant i_0: 0 <= i && i <= n;

        loop invariant i_1: a + b == 3 * i;

        loop invariant i_2: a >= 0;

        loop invariant i_3: b >= 0;


        loop assigns i;
        loop assigns b;
        loop assigns a;
    */
    while (i < n) {
        if (unknown1()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }

    //@ assert a + b == 3 * n;
    return 0;
}
