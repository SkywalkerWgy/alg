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
        loop invariant i_19: j == w;

        loop invariant i_20: i == z || (i >= z && i <= z + (w - \at(z, Pre)));

        loop invariant i_21: k == i - z;

        loop invariant i_22: x == z || (x >= z && x <= z + (w - \at(z, Pre)) + 1);

        loop invariant i_23: y == (w - \at(z, Pre)) - (x - z) || (y >= 0 && y <= (w - \at(z, Pre)));

        loop invariant i_24: w == x + y + 1;

        loop invariant i_25: z >= \at(z, Pre);


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_29: s for Loop B: ``` loop invariant i == \at(i, Pre) + k;

            loop invariant i_30: i == \at(i, Pre) + k;

            loop invariant i_31: k == i - \at(i, Pre);

            loop invariant i_32: \at(i, Pre) <= i <= j;

            loop invariant i_33: k >= 0;

            loop invariant i_34: j == \at(j, Pre);


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
            loop invariant i_35: x % 2 == 0 ==> y == \at(y, Pre) - (x - \at(x, Pre));

            loop invariant i_36: x % 2 == 1 ==> y == \at(y, Pre) - ((\at(x, Pre) % 2 == 0 ? x - \at(x, Pre) : x - \at(x, Pre) + 1));

            loop invariant i_37: y >= 0;

            loop invariant i_38: (x + y) == (\at(x, Pre) + \at(y, Pre));


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
        loop invariant i_26: a == b;

        loop invariant i_27: (flag ==> (a == c && b == d)) || (!flag ==> (a == \at(a, Pre) + c * (c + 1) / 2 && b == \at(b, Pre) + d * (d + 1) / 2));

        loop invariant i_28: c == d;


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