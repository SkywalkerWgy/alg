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
        loop invariant i_8: (flag ==> a == x + y - 1) && (!flag ==> a == x + y);

        loop invariant i_9: (a % 2 == 1 && flag ==> x % 2 == 0 && y % 2 == 1) || (a % 2 == 1 && !flag ==> x % 2 == 1 && y % 2 == 0);

        loop invariant i_10: (a % 2 == 0 && flag ==> x % 2 == 1 && y % 2 == 1) || (a % 2 == 0 && !flag ==> x % 2 == 0 && y % 2 == 1);


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