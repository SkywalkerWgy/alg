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
        loop invariant i_0: flag == \at(flag,Pre);

        loop invariant i_1: 1 <= x;

        loop invariant i_2: 1 <= y;

        loop invariant i_3: (x + y) % 2 == 0;

        loop invariant i_4: (flag != 0) ==> (a % 2 == 0);

        loop invariant i_5: (flag == 0) ==> (a % 2 == 1);


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