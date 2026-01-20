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
        loop invariant i_78: i == z && j == w && k == 0 && x % 2 == 1 && y == k;

        loop invariant i_79: i < j;

        loop invariant i_80: x >= z && y >= k && (x % 2 == 0 || y % 2 == 1);

        loop invariant i_81: a == 0 && b == 0 && c == 0 && d == 0;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_87: k >= 0;


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
            loop invariant i_88: x + y == z;

            loop invariant i_89: a >= 0 && b >= 0;

            loop invariant i_90: x % 2 == 1 || y % 2 == 1;

            loop invariant i_91: z <= w;

            loop invariant i_92: w == x + y + 1;


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
        loop invariant i_82: a >= 0 && b >= 0;

        loop invariant i_83: x % 2 == 1 || y % 2 == 1;

        loop invariant i_84: z <= w;

        loop invariant i_85: x + y == z;

        loop invariant i_86: w == x + y + 1;


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