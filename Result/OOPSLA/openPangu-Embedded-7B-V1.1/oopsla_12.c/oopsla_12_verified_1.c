int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_0: t == b;

        loop invariant i_1: s == a;

        loop invariant i_2: s + a == t;

        loop invariant i_3: t - s == b;

        loop invariant i_4: 0 <= s;

        loop invariant i_5: y >= 0 && y <= x;


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
        loop invariant i_6: y <= x;

        loop invariant i_7: t == b && s == a && s + a == t && t - s == b && 0 <= s && y >= 0 && y <= x;


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

