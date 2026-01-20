int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_24: t == b;

        loop invariant i_25: s == a + b;

        loop invariant i_26: s == t + a;

        loop invariant i_27: t == s + b;

        loop invariant i_28: 0 <= flag || t + s > 0;

        loop invariant i_29: y <= x;


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
        loop invariant i_30: t == b;

        loop invariant i_31: s == a + b;

        loop invariant i_32: s == t + a;

        loop invariant i_33: t == s + b;

        loop invariant i_34: 0 <= flag || t + s > 0;

        loop invariant i_35: y <= x;


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

