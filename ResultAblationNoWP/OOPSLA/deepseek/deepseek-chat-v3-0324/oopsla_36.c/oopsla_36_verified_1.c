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
        loop invariant i_0: z >= 0 && w >= 0;

        loop invariant i_1: i == z && j == w;

        loop invariant i_2: k == j - i ==> k >= 0;

        loop invariant i_3: x == z && y == k;

        loop invariant i_4: (x % 2 == 0) ==> (y == k);

        loop invariant i_5: (x % 2 == 1) ==> (y == k - 1);

        loop invariant i_6: w == x + y + 1;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_10: i <= j;

            loop invariant i_11: k == i - z;

            loop invariant i_12: z <= i <= w;

            loop invariant i_13: j == w;


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
            loop invariant i_14: x % 2 == 0 ==> y == k - (x - z) / 2;

            loop invariant i_15: x % 2 == 1 ==> y == (k - 1) - (x - z - 1) / 2;

            loop invariant i_16: y >= 0;

            loop invariant i_17: x >= z;

            loop invariant i_18: x + y == z + k - ((x - z) % 2);


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
        loop invariant i_7: a == b;

        loop invariant i_8: (flag ==> (a == c && b == d)) || (!flag ==> (a - c == \at(a - c, Pre) && b - d == \at(b - d, Pre)));

        loop invariant i_9: c == d;


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