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
        loop invariant i_0: flag ==> (a == x + y - 1);

        loop invariant i_1: !flag ==> (a == x + y);

        loop invariant i_2: (a % 2 == 1) <==> ((x + y) % 2 == 1);

        loop invariant i_3: flag ==> (x >= 1 && y >= 1);

        loop invariant i_4: !flag ==> (x >= 1 && y >= 1);


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