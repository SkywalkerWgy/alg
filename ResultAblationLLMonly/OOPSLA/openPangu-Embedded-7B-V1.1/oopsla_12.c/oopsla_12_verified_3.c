int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_8: t == b;

        loop invariant i_9: s == a;

        loop invariant i_10: a >= 0;

        loop invariant i_11: flag == flag;

        loop invariant i_12: y >= 0;

        loop invariant i_13: y == x + 2 * y;


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
        loop invariant i_14: y <= x;

        loop invariant i_15: t == b;

        loop invariant i_16: s == a;

        loop invariant i_17: a >= 0;

        loop invariant i_18: flag == flag;

        loop invariant i_19: y >= 0;

        loop invariant i_20: y == x + 2 * y;


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

