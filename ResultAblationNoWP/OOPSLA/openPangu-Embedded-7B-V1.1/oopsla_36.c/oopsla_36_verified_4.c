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
        loop invariant i_105: i >= k;

        loop invariant i_106: j >= w;

        loop invariant i_107: z % 2 == 1;

        loop invariant i_108: w == j;

        loop invariant i_109: x == z;

        loop invariant i_110: y == k;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_118: i >= k && j >= w && z % 2 == 1 && w == j && x == z && y == k;


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
            loop invariant i_119: i >= k && j >= w && z % 2 == 1 && w == j && x == z && y == k;

            loop invariant i_120: c >= 0 && d >= 0;


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
        loop invariant i_111: c >= 0 && d >= 0;

        loop invariant i_112: x == z;

        loop invariant i_113: i >= k;

        loop invariant i_114: j >= w;

        loop invariant i_115: z % 2 == 1;

        loop invariant i_116: w == j;

        loop invariant i_117: y == k;


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