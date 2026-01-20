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
        loop invariant i_0: a >= 0 && b >= 0 && c >= 0 && d >= 0 && x >= 0 && y >= 0;

        loop invariant i_1: a + c == x - d;

        loop invariant i_2: a + c + d == x;

        loop invariant i_3: b + d == y;

        loop invariant i_4: c >= 0 && b >= 0 && c + b == x - d;


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
            loop invariant i_5: a >= 0 && b >= 0 && c >= 0 && d >= 0 && x >= 0 && y >= 0;

            loop invariant i_6: a + c == x - d;

            loop invariant i_7: a + c + d == x;

            loop invariant i_8: b + d == y;

            loop invariant i_9: c >= 0 && b >= 0 && c + b == x - d;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}