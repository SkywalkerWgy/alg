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
        loop invariant i_0: z >= 0;

        loop invariant i_1: w >= z;

        loop invariant i_2: x % 2 == 0;

        loop invariant i_3: 0 <= k;

        loop invariant i_4: i >= j;

        loop invariant i_5: j <= w;

        loop invariant i_6: a == 0;

        loop invariant i_7: b == 0;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_18: z >= 0;

            loop invariant i_19: w >= z;

            loop invariant i_20: x % 2 == 0;

            loop invariant i_21: a == 0;

            loop invariant i_22: b == 0;

            loop invariant i_23: j == w;

            loop invariant i_24: i >= z;

            loop invariant i_25: i <= j;

            loop invariant i_26: 0 <= k;

            loop invariant i_27: i - k == z;


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
            loop invariant i_28: z >= 0;

            loop invariant i_29: w >= z;

            loop invariant i_30: a == 0;

            loop invariant i_31: b == 0;

            loop invariant i_32: j == w;

            loop invariant i_33: i >= z;

            loop invariant i_34: i <= j;

            loop invariant i_35: 0 <= k;

            loop invariant i_36: i - k == z;

            loop invariant i_37: x % 2 == 0;

            loop invariant i_38: x + y == w;


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
        loop invariant i_8: z >= 0;

        loop invariant i_9: w >= z;

        loop invariant i_10: x % 2 == 0;

        loop invariant i_11: 0 <= k;

        loop invariant i_12: i >= j;

        loop invariant i_13: j <= w;

        loop invariant i_14: c == d;

        loop invariant i_15: 0 <= c;

        loop invariant i_16: 0 <= d;

        loop invariant i_17: a - b == 0;


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