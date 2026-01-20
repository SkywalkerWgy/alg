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
        loop invariant i_51: i == z;

        loop invariant i_52: j == w;

        loop invariant i_53: k >= 0;

        loop invariant i_54: x % 2 == 0 || y % 2 == 1;

        loop invariant i_55: \forall integer t; x - y == (j - i + k);

        loop invariant i_56: w == j + k + x + y;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_62: k == j - i;


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
            loop invariant i_63: x == z + 2 * k;

            loop invariant i_64: y == w - k;

            loop invariant i_69: i == z;

            loop invariant i_70: j == w;

            loop invariant i_71: k >= 0;

            loop invariant i_72: x % 2 == 0 || y % 2 == 1;

            loop invariant i_73: w == j + k + x + y;

            loop invariant i_74: a == 0;

            loop invariant i_75: b == 0;

            loop invariant i_76: c >= 0;

            loop invariant i_77: d >= 0;


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
        loop invariant i_57: i == z;

        loop invariant i_58: j == w;

        loop invariant i_59: k >= 0;

        loop invariant i_60: x % 2 == 0 || y % 2 == 1;

        loop invariant i_61: w == j + k + x + y;

        loop invariant i_65: a == 0;

        loop invariant i_66: b == 0;

        loop invariant i_67: c >= 0;

        loop invariant i_68: d >= 0;


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