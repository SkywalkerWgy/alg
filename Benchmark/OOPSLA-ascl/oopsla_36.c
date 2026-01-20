int unknown1();
int unknown2();
int unknown3();

/*@
    requires a == 0;
    requires b == 0;
    requires x == 0;
    requires y == 0;
    requires z == 0;
    requires j == 0;
    requires w == 0;
    requires c == 0;
    requires d == 0;
    ensures  e_1: w >= z;
    ensures  e_2: a - b == 0;
*/
void oopsla_36(int flag, int a, int b, int x, int y, int z, int j, int w, int i, int k, int c, int d) {

    /*@
        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        /*@
            loop assigns k, i;
        */
        while (i < j) {
            k++;
            i++;
        }

        x = z;
        y = k;

        if (x % 2 == 1) {
            x++;
            y--;
        }

        /*@
            loop assigns x, y;
        */
        while (unknown2()) {
            if (x % 2 == 0) {
                x += 2;
                y -= 2;
            } else {
                x--;
                y--;
            }
        }
        z++;
        w = x + y + 1;
    }

    c = 0;
    d = 0;

    /*@
        loop assigns a, b, c, d;
    */
    while (unknown3()) {
        c++;
        d++;
        if (flag) {
            a++;
            b++;
        } else {
            a += c;
            b += d;
        }
    }
}
