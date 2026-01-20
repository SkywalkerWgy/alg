int unknown1();
int unknown2();


void oopsla_12(int flag){
    int t = 0;
    int s = 0;
    int a = 0;
    int b = 0;
    // Loop A
    /*@
        loop invariant i_0: a == b;

        loop invariant i_1: 0 <= a;

        loop invariant i_2: 0 <= b;

        loop invariant i_3: 0 <= s;

        loop invariant i_4: 0 <= t;

        loop invariant i_5: s == a * (a + 1) / 2;

        loop invariant i_6: (flag == 0) ==> (t == s);

        loop invariant i_7: (flag != 0) ==> (t == 2 * s);


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
        loop invariant i_8: a == b;

        loop invariant i_9: 0 <= a;

        loop invariant i_10: 0 <= b;

        loop invariant i_11: 0 <= s;

        loop invariant i_12: 0 <= t;

        loop invariant i_13: s == a * (a + 1) / 2;

        loop invariant i_14: (flag == 0) ==> (t == s);

        loop invariant i_15: (flag != 0) ==> (t == 2 * s);

        loop invariant i_16: (flag == 0) ==> x == 1;

        loop invariant i_17: (flag != 0) ==> x == 2;

        loop invariant i_18: 0 <= y;

        loop invariant i_19: y <= 4;


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

