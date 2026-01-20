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
        loop invariant i_0: a + c == b + d;

        loop invariant i_1: c - b == 1;

        loop invariant i_2: x == y;

        loop invariant i_3: (x + y) % 2 == 0;


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
            loop invariant i_4: a + c == b + d;

            loop invariant i_5: c - b == 1;

            loop invariant i_6: x == y;

            loop invariant i_7: (x + y) % 2 == 0;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}