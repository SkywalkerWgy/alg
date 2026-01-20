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

        loop invariant i_8: flag ==> t == s + a*b - a;


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

        loop invariant i_9: y <= x + 1;

        loop invariant i_10: (flag ==> x <= 2) && (!flag ==> x == 1);


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

