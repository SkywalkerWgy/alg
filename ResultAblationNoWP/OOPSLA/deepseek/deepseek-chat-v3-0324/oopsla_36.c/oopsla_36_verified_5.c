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
        loop invariant i_75: z >= 0 && w >= 0;

        loop invariant i_76: w == x + y + 1;

        loop invariant i_77: j == \at(w, Pre);

        loop invariant i_78: i == \at(z, Pre);

        loop invariant i_79: k == j - i;

        loop invariant i_80: x % 2 == 0;

        loop invariant i_81: y >= 0;

        loop invariant i_82: z == \at(z, Pre) + \at(k, Pre);


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_90: s for Loop B: ``` loop invariant i <= j;

            loop invariant i_91: i <= j;

            loop invariant i_92: k == i - \at(i, Pre);

            loop invariant i_93: \at(j, Pre) == j;

            loop invariant i_94: z == \at(z, Pre);

            loop invariant i_95: w == \at(w, Pre);

            loop invariant i_96: x == \at(x, Pre);

            loop invariant i_97: y == \at(y, Pre);


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
            loop invariant i_98: x % 2 == 0 && y >= 0;

            loop invariant i_99: x + y == \at(x, Pre) + \at(y, Pre);

            loop invariant i_100: (x % 2 == 0) ==> (y % 2 == 0);

            loop invariant i_101: (x % 2 == 1) ==> (y % 2 == 1);


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
        loop invariant i_83: s for Loop D: ``` loop invariant a == b;

        loop invariant i_84: a == b;

        loop invariant i_85: flag ==> (a == c && b == d);

        loop invariant i_86: !flag ==> (a - b == c - d);

        loop invariant i_87: c == d;

        loop invariant i_88: \at(c, Pre) <= c <= \at(c, LoopEntry);

        loop invariant i_89: \at(d, Pre) <= d <= \at(d, LoopEntry);


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