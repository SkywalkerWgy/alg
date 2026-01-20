int unknown1();
int unknown2();
int unknown3();

void oopsla_29() {
    int a = 1;
    int b = 1;
    int c = 2;
    int d = 2;
    int x = 3;
    int y = 3;

    // Loop A
    /*@
        loop invariant i_3: a + c == b + d && (x + y) % 2 == 1;


        loop assigns y, x, d, a, c, b;
    */
    while (unknown1()) {
        x = a + c;
        y = b + d;
        if ((x + y) % 2 == 0) {
            a++;
            d++;
        } 
        else {
            a--;
        }

        // Loop B
        /*@
            loop invariant i_4: \forall integer k; 0 <= k < i ==> max >= a[k];

            loop invariant i_5: \exists integer k; 0 <= k < i && max == a[k];

            loop invariant i_6: a <= max;

            loop invariant i_7: a + c == b + d;

            loop invariant i_8: (x + y) % 2 == 1;

            loop invariant i_9: \forall integer k; 0 <= k < i ==> a[k] <= max;

            loop invariant i_10: \forall integer p; 0 <= p < \at(k, End_l) ==> res[p] == \at(res[p], End_l);


            loop assigns y, x, d, a, c, b;
        */
        while (unknown2()) {
            c--;
            b--;
        }
    }
    
    //@ assert  a_1: a + c == b + d;
}