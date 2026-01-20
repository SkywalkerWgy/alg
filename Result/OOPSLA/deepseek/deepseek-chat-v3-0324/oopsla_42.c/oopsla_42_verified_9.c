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
        loop invariant i_0: (flag ==> a == x + y - 2) && (!flag ==> a == x + y - 1);

        loop invariant i_2: a % 2 == (flag ? 0 : 1);

        loop invariant i_3: (flag ==> (x - y) % 2 == a % 2) && (!flag ==> (x - y) % 2 != a % 2);

        loop invariant i_4: (flag ==> (x - y) % 2 == 0) && (!flag ==> (x - y + 1) % 2 == 0);

        loop invariant i_6: (flag ==> (x - y + 2) % 2 == 0) && (!flag ==> (x - y + 1) % 2 == 1);

        loop invariant i_7: (flag ==> a == (flag ? 0 : 1)) && (!flag ==> a == (flag ? 0 : 1));

        loop invariant i_8: x == 1 && y == 1;

        loop invariant i_9: (flag ==> (a + 1) % 2 == (x - y) % 2 || (x == 1 && y == 1)) && (!flag ==> a % 2 == (x - y + 1) % 2 || (x == 1 && y == 1));

        loop invariant i_10: (x == 1 && y == 1) || (flag ==> (x - y) % 2 == 0) && (!flag ==> (x - y) % 2 == 1);

        loop invariant i_11: (x == 1 && y == 1) || (flag ==> (x - y) % 2 == 0) && (!flag ==> (x - y + 1) % 2 == 0);

        loop invariant i_12: (x == 1 && y == 1) || (flag ==> (x - y + 2) % 2 == 0) && (!flag ==> (x - y + 1) % 2 == 1);

        loop invariant i_13: (x == 1 && y == 1) || (flag ==> (a + 1) % 2 == (x - y) % 2) && (!flag ==> a % 2 == (x - y + 1) % 2);

        loop invariant i_14: (x == 1 && y == 1) || ((flag ==> (a + 1) % 2 == (x - y) % 2) && (!flag ==> a % 2 == (x - y + 1) % 2));

        loop invariant i_15: (flag ==> a == (x == 1 && y == 1 ? (flag ? 0 : 1) : x + y - (flag ? 2 : 1))) && (!flag ==> a == (x == 1 && y == 1 ? (flag ? 0 : 1) : x + y - (flag ? 2 : 1)));


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