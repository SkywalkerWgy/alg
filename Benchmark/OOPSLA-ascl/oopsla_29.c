int unknown1();
int unknown2();
int unknown3();

/*@
    requires a == 1;
    requires b == 1;
    requires c == 2;
    requires d == 2;
    requires x == 3;
    requires y == 3;
    ensures e_1: a + c == b + d;
*/
void oopsla_29(int a, int b, int c, int d, int x, int y) {

    /*@
        loop assigns y, x, d, a;
    */
    while (unknown1()) {
        x = a + c;
        y = b + d;
        if ((x + y) % 2 == 0) {
            a++;
            d++;
        } else {
            a--;
        }

        /*@
            loop assigns c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
}
