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
        loop invariant i_2: 1 <= x && 1 <= y;

        loop invariant i_3: 1 <= a <= 2 * x + y && (flag == 0 => a == x + y + 1);

        loop invariant i_4: a % 2 == 1 || flag == 1;

        loop invariant i_5: \exists int k; 0 <= k && k == i && a == x + y + 1;

        loop invariant i_6: \forall int k; 0 <= k < i ==> a % 2 == 1;

        loop invariant i_7: \exists int k; 0 <= k < i && a == x + y + 1;

        loop invariant i_8: flag == 0 => a == x + y + 1;

        loop invariant i_9: flag == 1 => a == x + y;

        loop invariant i_10: 1 <= a && 1 <= x + y + (flag ? 0 : 1);

        loop invariant i_11: \forall int k; 0 <= k < i ∧ a % 2 == 1;

        loop invariant i_12: \exists int k; 0 <= k < i ∧ a == x + y + 1;

        loop invariant i_13: flag == 0 ⇒ a == x + y + 1;

        loop invariant i_14: flag == 1 ⇒ a == x + y;

        loop invariant i_15: a ≡ x + y + (flag ? 0 : 1);

        loop invariant i_16: 1 <= a <= x + y + 1;

        loop invariant i_17: \forall int k; 0 <= k < i ⇒ a % 2 == 1;

        loop invariant i_18: \exists int k; 0 <= k < i && a == x + y +;


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