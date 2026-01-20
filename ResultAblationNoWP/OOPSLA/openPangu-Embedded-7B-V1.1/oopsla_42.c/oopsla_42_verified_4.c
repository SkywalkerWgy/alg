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
        loop invariant i_21: a >= 0;

        loop invariant i_22: y >= 0;

        loop invariant i_23: x >= 0;

        loop invariant i_24: flag == false || (a % 2 == 1 && x == y);

        loop invariant i_25: a % 2 == 1 || flag == true;

        loop invariant i_26: \exists integer k; 0 <= k < unknown1();


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