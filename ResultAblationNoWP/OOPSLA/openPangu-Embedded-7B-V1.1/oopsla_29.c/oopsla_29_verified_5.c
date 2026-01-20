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
        loop invariant i_21: a >= b && c >= d;

        loop invariant i_22: x == y;

        loop invariant i_23: (x + y) % 2 == 0 && a == b || c == d;

        loop invariant i_24: x <= y;


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
            loop invariant i_25: b == c && a == d;

            loop invariant i_26: c == b + d;

            loop invariant i_27: x == y;

            loop invariant i_28: \forall integer k; 0 <= k < i ==> c == b + d;

            loop invariant i_29: \exists integer k; 0 <= k < i && c == b + d;

            loop invariant i_30: \forall integer k; 0 <= k < i ==> x == y;

            loop invariant i_31: \forall integer k; 0 <= k < i ==> (x + y) % 2 == 0 && a == b || c == d;

            loop invariant i_32: \forall integer k; 0 <= k < i ==> x <= y;

            loop invariant i_33: a >= b && c >= d;

            loop invariant i_34: (x + y) % 2 == 0 && a == b || c == d;

            loop invariant i_35: x <= y;

            loop invariant i_36: \forall integer k; 0 <= k < i ==> a >= b && c >= d;


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}