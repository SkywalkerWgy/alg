int unknown1();
int unknown2();
int unknown3();

void oopsla_36(int flag) {
    int a = 0;
    int b = 0;
    int x = 0;
    int y = 0;
    int z = 0;
    int w = 0;
    int j = w;
    int i = z;
    int k = 0;

    // Loop A
    /*@
        loop invariant i_37: i == z && j == w && k == 0 && x % 2 == 1 && y == k && z >= x && w >= y && a == b && c == 0 && d == 0;

        loop invariant i_38: i < j;

        loop invariant i_39: x % 2 == 0 || (x == z && y == 0);

        loop invariant i_40: a == b && c == d && flag == 0 || (flag == 1 ==> a == b + c && d == b + d);


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_44: i == z && k == 0;

            loop invariant i_45: x % 2 == 1 && y == k;

            loop invariant i_46: c == 0 && d == 0 && flag == 0;

            loop invariant i_47: k == 0;

            loop invariant i_48: a == b && x == z && y == k && z >= x && w >= y;

            loop invariant i_49: \forall integer n; n < z ==> a >= b + n;


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

        // Loop C
        /*@
            loop invariant i_50: x % 2 == 1 && y == k && z >= x && w >= y && a == b && i == z && j == w && k == 0;


            loop assigns x, y;
        */
        while (unknown2()) {
            if (x % 2 == 0) {
                x += 2;
                y -= 2;
            } 
            else {
                x--;
                y--;
            }
        }
        z++;
        w = x + y + 1;
    }

    int c = 0;
    int d = 0;
    
    // Loop D
    /*@
        loop invariant i_41: c == 0 && d == 0 && flag == 0;

        loop invariant i_42: k == 0;

        loop invariant i_43: i == z && j == w && k == 0 && x % 2 == 1 && y == k && z >= x && w >= y && a == b && c == 0 && d == 0;


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

    //@ assert a_1: (w >= z && a - b == 0);
}