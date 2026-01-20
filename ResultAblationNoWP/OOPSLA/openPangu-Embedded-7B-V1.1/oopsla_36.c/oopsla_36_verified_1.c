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
        loop invariant i_0: i <= j;

        loop invariant i_1: k <= i;

        loop invariant i_2: x % 2 == 0 || y % 2 == 1;

        loop invariant i_3: z <= x;

        loop invariant i_4: w == j;

        loop invariant i_5: \forall integer k; 0 <= k < i ==> max >= a[k];

        loop invariant i_6: \exists integer k; 0 <= k < i && max == a[k];


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_15: k <= i;


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
            loop invariant i_16: x % 2 == 0 || y % 2 == 1;

            loop invariant i_17: z <= x;

            loop invariant i_18: w == j;

            loop invariant i_19: \forall integer k; 0 <= k < i ==> max >= a[k];

            loop invariant i_20: \exists integer k; 0 <= k < i && max == a[k];

            loop invariant i_21: a <= b;

            loop invariant i_22: b >= a;


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
        loop invariant i_7: w == j;

        loop invariant i_8: k <= i;

        loop invariant i_9: x % 2 == 0 || y % 2 == 1;

        loop invariant i_10: z >= x;

        loop invariant i_11: \forall integer k; 0 <= k < i ==> max >= a[k];

        loop invariant i_12: \exists integer k; 0 <= k < i && max == a[k];

        loop invariant i_13: a <= b;

        loop invariant i_14: b >= a;


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