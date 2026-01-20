int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_23: t == b;

        loop invariant i_24: s == a;

        loop invariant i_25: s >= t;

        loop invariant i_26: a <= t;

        loop invariant i_27: s >= a;

        loop invariant i_28: t <= s;

        loop invariant i_29: 0 <= a || flag;

        loop invariant i_30: 0 <= b || flag;

        loop invariant i_31: y <= x;


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
        loop invariant i_32: y == x;

        loop invariant i_33: t == b && s == a && a == 0 || flag && b == 0;

        loop invariant i_34: y <= x;


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

