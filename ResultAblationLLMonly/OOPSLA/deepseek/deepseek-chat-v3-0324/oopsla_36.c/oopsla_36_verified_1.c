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

        loop invariant i_1: z <= w;

        loop invariant i_2: x >= 0 && y >= 0;

        loop invariant i_3: w == x + y + 1;

        loop invariant i_4: z == \at(z, Pre) + \count;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_5: i <= j;

            loop invariant i_6: k == i - \at(i, Pre);

            loop invariant i_7: i >= \at(i, Pre);

            loop invariant i_8: j == \at(j, Pre);


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
            loop invariant i_9: x + y == \at(x, Pre) + \at(y, Pre);

            loop invariant i_10: x % 2 == 0;


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
        loop invariant i_11: c == d;

        loop invariant i_12: flag ==> a == b;

        loop invariant i_13: !flag ==> a - b == c - d;


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