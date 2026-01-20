int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_19: t >= 0 && s >= 0 && a >= 0 && b >= 0;

        loop invariant i_20: y <= x;


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
        loop invariant i_21: t >= 0 && s >= 0 && a >= 0 && b >= 0 && y <= x;

        loop invariant i_22: y <= x && y >= 0;


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

