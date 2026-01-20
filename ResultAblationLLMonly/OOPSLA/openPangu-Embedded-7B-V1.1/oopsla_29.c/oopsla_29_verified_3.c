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
        loop invariant i_13: a >= 0 && b >= 0 && c >= 0 && d >= 0 && x >= 0 && y >= 0;

        loop invariant i_14: a + c == x && b + d == y;

        loop invariant i_15: x + y == a + b + c + d;

        loop invariant i_16: x % 2 == y % 2;

        loop invariant i_17: (x + y) % 2 == 0 && (a + c) % 2 == (b + d) % 2;

        loop invariant i_18: c >= 0 && b >= 0;

        loop invariant i_19: b >= 0 && c == b;

        loop invariant i_20: b + c == x + y;


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
            loop invariant i_21: x + y == a + b + c + d;

            loop invariant i_22: x % 2 == y % 2;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}