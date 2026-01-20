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
        loop invariant i_39: z >= 0;

        loop invariant i_40: w >= z;

        loop invariant i_41: (x % 2 == 0) ==> (y >= 0);

        loop invariant i_42: (x % 2 == 1) ==> (y >= 1);

        loop invariant i_43: w == x + y + 1;

        loop invariant i_44: \at(z, Pre) <= z <= \at(z, Pre) + \at(unknown1(), Pre);

        loop invariant i_45: \at(w, Pre) <= w <= \at(w, Pre) + \at(unknown1(), Pre);


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_50: i <= j;

            loop invariant i_51: k == i - \at(i, Pre);

            loop invariant i_52: \at(i, Pre) <= i <= j;

            loop invariant i_53: k >= 0;


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
            loop invariant i_54: (x % 2 == 0) ==> (y >= 0);

            loop invariant i_55: (x % 2 == 1) ==> (y >= 1);

            loop invariant i_56: w == x + y + 1;


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
        loop invariant i_46: a == b;

        loop invariant i_47: c == d;

        loop invariant i_48: flag ==> (a == c && b == d);

        loop invariant i_49: !flag ==> (a >= c && b >= d);


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