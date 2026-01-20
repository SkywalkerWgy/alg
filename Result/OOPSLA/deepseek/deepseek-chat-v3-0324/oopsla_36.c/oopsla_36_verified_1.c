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
        loop invariant i_0: a == 0 && b == 0;

        loop invariant i_1: w >= z;

        loop invariant i_2: x == \old(z) + 1 || x == \old(z);

        loop invariant i_3: y == \old(k) - 1 || y == \old(k);

        loop invariant i_4: z == \old(z) + 1;

        loop invariant i_5: w == x + y + 1;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_7: i <= j;

            loop invariant i_8: k == i - \at(i, Pre_loop);

            loop invariant i_9: \at(i, Pre_loop) <= i <= j;

            loop invariant i_10: k >= 0;


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
            loop invariant i_12: x + 2*y == \old(x) + 2*\old(y);

            loop invariant i_13: x % 2 == 0;

            loop invariant i_14: y >= 0;


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
        loop invariant i_15: a == b;

        loop invariant i_16: c == d;

        loop invariant i_17: \at(a, Pre_loop) <= a <= \at(a, Pre_loop) + c;

        loop invariant i_18: \at(b, Pre_loop) <= b <= \at(b, Pre_loop) + d;

        loop invariant i_19: flag ==> (a == \at(a, Pre_loop) + c && b == \at(b, Pre_loop) + d);

        loop invariant i_20: !flag ==> (a == \at(a, Pre_loop) + c && b == \at(b, Pre_loop) + d);


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