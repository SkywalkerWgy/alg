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
        loop invariant i_55: i == z;

        loop invariant i_56: j == w;

        loop invariant i_57: k == 0 || i < j;

        loop invariant i_58: x == z || x % 2 == 0;

        loop invariant i_59: y == k || x % 2 == 1;

        loop invariant i_60: w == j;

        loop invariant i_61: z >= x;

        loop invariant i_62: x + y == z;

        loop invariant i_63: x % 2 == y;

        loop invariant i_64: y == k;

        loop invariant i_65: w == x + y + 1;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_80: i == z;

            loop invariant i_81: j == w;

            loop invariant i_82: k == 0 || i < j;

            loop invariant i_83: x == z || x % 2 == 0;

            loop invariant i_84: y == k || x % 2 == 1;

            loop invariant i_85: w == j;

            loop invariant i_86: z >= x;

            loop invariant i_87: x + y == z;

            loop invariant i_88: x % 2 == y;

            loop invariant i_89: y == k;

            loop invariant i_90: w == x + y + 1;


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
            loop invariant i_91: i == z;

            loop invariant i_92: j == w;

            loop invariant i_93: k == 0 || i < j;

            loop invariant i_94: x == z || x % 2 == 0;

            loop invariant i_95: y == k || x % 2 == 1;

            loop invariant i_96: w == j;

            loop invariant i_97: z >= x;

            loop invariant i_98: x + y == z;

            loop invariant i_99: x % 2 == y;

            loop invariant i_100: y == k;

            loop invariant i_101: w == x + y + 1;

            loop invariant i_102: a >= c;

            loop invariant i_103: b >= d;

            loop invariant i_104: a - b == 0 && w == x + y + 1;


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
        loop invariant i_66: i == z;

        loop invariant i_67: j == w;

        loop invariant i_68: k == 0 || i < j;

        loop invariant i_69: x == z || x % 2 == 0;

        loop invariant i_70: y == k || x % 2 == 1;

        loop invariant i_71: w == j;

        loop invariant i_72: z >= x;

        loop invariant i_73: x + y == z;

        loop invariant i_74: x % 2 == y;

        loop invariant i_75: y == k;

        loop invariant i_76: w == x + y + 1;

        loop invariant i_77: a >= c;

        loop invariant i_78: b >= d;

        loop invariant i_79: a - b == 0 && w == x + y + 1;


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