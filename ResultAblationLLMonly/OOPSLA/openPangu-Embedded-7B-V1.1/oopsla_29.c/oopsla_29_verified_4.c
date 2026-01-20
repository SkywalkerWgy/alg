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
        loop invariant i_23: a >= 0;

        loop invariant i_24: b >= 0;

        loop invariant i_25: c <= x;

        loop invariant i_26: d <= x;

        loop invariant i_27: x <= x + c;

        loop invariant i_28: y <= y + d;


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
            loop invariant i_29: a >= 0;

            loop invariant i_30: b >= 0;

            loop invariant i_31: c <= x;

            loop invariant i_32: d <= x;

            loop invariant i_33: x <= x + c;

            loop invariant i_34: y <= y + d;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}