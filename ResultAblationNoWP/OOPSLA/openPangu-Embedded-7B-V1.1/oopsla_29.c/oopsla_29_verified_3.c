int unknown1();
int unknown2();
int unknown3();

void oopsla_29() {
    int a = 1;
    int b = 1;
    int c = 2;
    int d = 2;
    int x = 3;
    int y = 3;

    // Loop A
    /*@
        loop invariant i_11: a + c == b + d;


        loop assigns y, x, d, a, c, b;
    */
    while (unknown1()) {
        x = a + c;
        y = b + d;
        if ((x + y) % 2 == 0) {
            a++;
            d++;
        } 
        else {
            a--;
        }

        // Loop B
        /*@
            loop invariant i_12: a + c == b + d;

            loop invariant i_13: b + d == a + c;

            loop invariant i_14: \forall int i; i < i_11 ==> a + c == b + d;

            loop invariant i_15: a + c == b + d: loop assigns y, x, d, a, c, b;

            loop invariant i_16: for the following loop. loop assigns y, x, d, a, c, b;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}