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
        loop invariant i_23: a >= b && a - b == c - d;

        loop invariant i_24: i < j && k == 0 && x == z && y == k;

        loop invariant i_25: w == j;

        loop invariant i_26: x % 2 == 1 || x == y;

        loop invariant i_27: z % 2 == 1 || x == y;

        loop invariant i_28: \forall integer k; 0 <= k < j && w == z || k == 0;

        loop invariant i_29: \exists integer k; 0 <= k < j && w == z;

        loop invariant i_30: \forall integer p; 0 <= p < \at(k, End_l) && res[p] == \at(res[p], End_l);

        loop invariant i_31: \forall integer k; 0 <= k < i ==> x >= k && y >= k;

        loop invariant i_32: \forall integer k; 0 <= k < i && x == y;

        loop invariant i_33: \forall integer k; 0 <= k < i && x % 2 == \at(res[k], End_l) % 2;

        loop invariant i_34: \forall integer k; 0 <= k < i && y % 2 == \at(res[k], End_l) % 2;

        loop invariant i_35: \forall integer k; 0 <= k < i && z % 2 == \at(res[k], End_l) % 2;

        loop invariant i_36: \forall integer k; 0 <= k < i && z == x || z == y;

        loop invariant i_37: \forall integer k; 0 <= k < i && w == z || k == 0;


        loop assigns i, j, k, x, y, z, w;
    */
    while (unknown1()) {
        i = z;
        j = w;
        k = 0;

        // Loop B
        /*@
            loop invariant i_53: i < j && k == 0 && x == z && y == k && w == j;


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
            loop invariant i_54: i < j && k == 0 && x == z && y == k && w == j;


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
        loop invariant i_38: a >= b && a - b == c - d;

        loop invariant i_39: i < j && k == 0 && x == z && y == k;

        loop invariant i_40: w == j;

        loop invariant i_41: x % 2 == 1 || x == y;

        loop invariant i_42: z % 2 == 1 || x == y;

        loop invariant i_43: \forall integer k; 0 <= k < j && w == z || k == 0;

        loop invariant i_44: \exists integer k; 0 <= k < i && w == z;

        loop invariant i_45: \forall integer p; 0 <= p < \at(k, End_l) && res[p] == \at(res[p], End_l);

        loop invariant i_46: \forall integer k; 0 <= k < i ==> x >= k && y >= k;

        loop invariant i_47: \forall integer k; 0 <= k < i && x == y;

        loop invariant i_48: \forall integer k; 0 <= k < i && x % 2 == \at(res[k], End_l) % 2;

        loop invariant i_49: \forall integer k; 0 <= k < i && y % 2 == \at(res[k], End_l) % 2;

        loop invariant i_50: \forall integer k; 0 <= k < i && z % 2 == \at(res[k], End_l) % 2;

        loop invariant i_51: \forall integer k; 0 <= k < i && z == x || z == y;

        loop invariant i_52: \forall integer k; 0 <= k < i && w == z || k == 0;


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