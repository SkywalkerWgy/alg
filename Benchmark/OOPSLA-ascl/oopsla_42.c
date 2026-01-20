int unknown1();
int unknown2();

/*@
    ensures  e_1: a % 2 == 1;
*/
void oopsla_42(int flag, int x, int y, int a) {

    x = 1;
    y = 1;

    if (flag)
        a = 0;
    else
        a = 1;

    /*@
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
}
