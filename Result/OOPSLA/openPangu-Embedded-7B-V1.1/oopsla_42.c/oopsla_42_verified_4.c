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