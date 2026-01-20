int unknown1();
int unknown2();

void oopsla_42(int flag) {
    int x = 1;
    int y = 1;
    int a;

    if (flag)
        a = 0;
    else
        a = 1;

    // Loop A
    /*@
        loop invariant i_0: 0 <= a;

        loop invariant i_1: y >= 0;

        loop invariant i_2: x == y || a == x;

        loop invariant i_3: x == y || a == x || a == y;

        loop invariant i_4: x + a >= 0 && y + a >= 0;

        loop invariant i_5: x + a >= 0 && y + a >= 0 && x + y == x + y;

        loop invariant i_6: x >= 0 && y >= 0 && a == x || a == y || (x == y + 1 || x + a == y || y + a == x);

        loop invariant i_7: 0 <= y;

        loop invariant i_8: x + y == x + y;

        loop invariant i_9: x >= 0 && y >= 0;

        loop invariant i_10: x >= 0 && y >= 0 && x + y == x + y;

        loop invariant i_11: 0 <= x;

        loop invariant i_12: x >= 0 && y >= 0 && (x == y || a == x || a == y || (x == y + 1 || x + a == y || y + a == x));

        loop invariant i_13: x + y + a >= 0;

        loop invariant i_14: (flag ? x + a == y : y + a == x) && (flag ? 1 : 0);

        loop invariant i_15: x + y + a % 2 == x + y;

        loop invariant i_16: (flag ? x : y) + a >= 0 && (flag ? y : x) + a >= 0;

        loop invariant i_17: (flag ? x : y) >= 0 && (flag ? y : x) >= 0;

        loop invariant i_18: (flag ? x + a : y + a) >= 0;

        loop invariant i_19: (flag ? x : y) + a == (flag ? x + 1 : y + 1);

        loop invariant i_20: (flag ? x : y) + a >= 0;

        loop invariant i_21: (flag ? x : y) + a == (flag ? x : y) + 1;

        loop invariant i_22: x + a >= 0 && y + a >= 0 && (flag ? x : y) + a == (flag ? x : y) + 1;

        loop invariant i_23: i;


        loop assigns a, x, y;
    */
    while (unknown1()) {
        if (flag) {
            a = x + y;
            x++;
        } else {
            a = x + y + 1;
            y++;
        }
        if (a % 2 == 1)
            y++;
        else
            x++;
    }

    if (flag)
        a++;

    //@ assert a_1: (a % 2 == 1);
}