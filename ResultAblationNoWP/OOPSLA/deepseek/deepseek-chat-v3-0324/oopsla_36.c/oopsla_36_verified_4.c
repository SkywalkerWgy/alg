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
        loop invariant i_57: z >= 0 && w >= z;

        loop invariant i_58: w == x + y + 1;

        loop invariant i_59: x == z + k;

        loop invariant i_60: y >= 0;

        loop invariant i_61: i == z && j == w ==> k == 0;

        loop invariant i_62: i == z + k && j == w ==> k >= 0;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_65: j == w;

            loop invariant i_66: z <= i <= j;

            loop invariant i_67: k == i - z;

            loop invariant i_68: i >= z;


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
            loop invariant i_69: s for Loop C: ``` loop invariant x + y == z + k;

            loop invariant i_70: x + y == z + k;

            loop invariant i_71: y >= 0;

            loop invariant i_72: x >= z;

            loop invariant i_73: (x % 2 == 0) ==> (y % 2 == k % 2);

            loop invariant i_74: (x % 2 == 1) ==> (y % 2 != k % 2);


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
        loop invariant i_63: c == d;

        loop invariant i_64: a == b;


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