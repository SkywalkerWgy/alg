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
        loop invariant i_5: (flag ==> (a == x + y - 1)) && (!flag ==> (a == x + y));

        loop invariant i_6: (a % 2 == 1) == (flag ? (x % 2 != y % 2) : (x % 2 == y % 2));

        loop invariant i_7: x >= 1 && y >= 1;


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