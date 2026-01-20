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
        loop invariant i_15: i >= j;

        loop invariant i_16: k < z;

        loop invariant i_17: x % 2 == y % 2;

        loop invariant i_18: z >= x + y;

        loop invariant i_19: w == x + y + 1 - z;

        loop invariant i_20: a <= b;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_27: k >= 0;

            loop invariant i_28: x >= 0 && y >= 0;

            loop invariant i_29: a <= b;

            loop invariant i_30: c <= d;

            loop invariant i_31: flag == false || a == 0 && b == 0;


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
            loop invariant i_32: x % 2 == y % 2;

            loop invariant i_33: z >= x + y;

            loop invariant i_34: w == x + y + 1 - z;


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
        loop invariant i_21: i >= j;

        loop invariant i_22: k < z;

        loop invariant i_23: x % 2 == y % 2;

        loop invariant i_24: z >= x + y;

        loop invariant i_25: w == x + y + 1 - z;

        loop invariant i_26: a <= b;

        loop invariant i_35: c < z;

        loop invariant i_36: d < z;


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