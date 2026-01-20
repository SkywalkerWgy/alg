int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_0: s == (a*(a + 1))/2;

        loop invariant i_1: flag ==> t == s + a*b;

        loop invariant i_2: !flag ==> t == s;

        loop invariant i_3: a == b;

        loop invariant i_11: !flag ==> t == (b*(b + 1))/2;

        loop invariant i_12: flag ==> t == (b*(b + 1))/2 + a*b - a;

        loop invariant i_16: flag ==> t == s + a*b - a*b + a;

        loop invariant i_17: flag ==> t == s + a*(b - (b - 1));

        loop invariant i_18: flag ==> a == b ==> t == s + a*a - a;

        loop invariant i_19: flag ==> t == s + a*(b - 1);

        loop invariant i_23: flag ==> t == s + a*b - a + b;

        loop invariant i_24: flag ==> t == s + a*(b + 1) - a;

        loop invariant i_27: flag ==> t == s + a*b - a*(b-1);

        loop invariant i_28: flag ==> t == s + a;

        loop invariant i_33: flag ==> t == s + a*(b - 1) + b;

        loop invariant i_34: flag ==> a == b ==> t == s + a*(a - 1) + a;

        loop invariant i_40: flag ==> t == (b*(b + 1))/2 + a*b;

        loop invariant i_41: flag ==> s == (a*(a + 1))/2;

        loop invariant i_42: flag ==> a == b;


        loop assigns t;
        loop assigns s;
        loop assigns b;
        loop assigns a;
    */
    while(unknown1()) {
        a++;
        b++;
        s += a;
        t += b;
        if(flag) {
            t += a;
        }
    } 

    int x = 1;
    if(flag) {
        x = t - 2*s + 2;
    }
    int y = 0;

    // Loop B
    /*@
        loop invariant i_4: y >= 0;

        loop invariant i_5: x >= 1 ==> y <= x + 2;

        loop invariant i_6: !flag ==> x == 1;

        loop invariant i_7: flag ==> x == t - 2*s + 2;

        loop invariant i_10: (flag ==> x <= 2) && (!flag ==> x == 1);

        loop invariant i_13: y <= x + 2;

        loop invariant i_14: x <= 2 ==> y <= 3;

        loop invariant i_20: x >= 0;

        loop invariant i_25: x <= 1 || (flag && x == 2);

        loop invariant i_26: y <= x + (x == 2 ? 2 : 1);

        loop invariant i_29: x <= 2;

        loop invariant i_30: x == 2 ==> (flag && y <= 4);

        loop invariant i_31: x == 1 ==> y <= 3;

        loop invariant i_32: y <= x + (x == 1 ? 2 : 2);

        loop invariant i_35: x <= 2 && flag ==> y <= x + 2;

        loop invariant i_36: x == 2 && flag ==> y <= 4;

        loop invariant i_37: y <= x + (flag && x == 2 ? 2 : 1);

        loop invariant i_38: (flag && x == 2) ==> y <= 4;

        loop invariant i_39: (!flag) ==> y <= 2;

        loop invariant i_43: x <= 2 ==> y <= 4;

        loop invariant i_44: x == 2 ==> y <= 4;

        loop invariant i_45: y <= 2 * x;

        loop invariant i_46: x <= 2 ==> y <= 2 * x;

        loop invariant i_47: x == 2 ==> y <= 2;

        loop invariant i_48: x == 1 ==> y <= 1;

        loop invariant i_49: y <= x + 1;

        loop invariant i_50: y <= (x == 2 ? 2 : 1);

        loop invariant i_51: y <= x + (x == 2 ? 1 : 1);


        loop assigns y;
    */
    while(y <= x){
        if(unknown2()) {
            y++;
        }
        else{ 
            y += 2;
    
        }
    }

    //@ assert  a_1: y <= 4;
}

