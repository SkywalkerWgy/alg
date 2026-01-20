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

        loop invariant i_1: x == a + c;

        loop invariant i_2: y == b + d;

        loop invariant i_6: x == y;


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
            loop invariant i_3: a + c == b + d;

            loop invariant i_5: y == b + d;

            loop invariant i_7: x == y;

            loop invariant i_8: x == a + c || b == d;

            loop invariant i_9: y == b + d || a == c;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}