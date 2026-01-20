int unknown1();
int unknown2();
int unknown3();

void oopsla_33(int k){
    int z = k;
    int x = 0;
    int y = 0;
    int c = 0;

    // Loop A
    /*@
        loop invariant i_2: x >= 0;

        loop invariant i_3: z >= y - c && z - y == c;

        loop invariant i_4: z % 2 == 1 || x == y;

        loop invariant i_5: \forall integer i; 0 <= i < k < i ==> x <= y;

        loop invariant i_10: x <= y;

        loop invariant i_11: z % 2 == 1;

        loop invariant i_12: x == y;

        loop invariant i_13: z - y >= c;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_7: x == y && c == 0;

            loop invariant i_9: x == y;


            loop assigns  y, x, c;
        */
        while(unknown2()){
            if(z==k+y-c){
                x++;
                y++;
                c++;
            }
            else{
                x++;
                y--;
                c++;
            }
        }
        // Loop C
        /*@
            loop invariant i_6: x == y;


            loop assigns y;
            loop assigns x;
        */
        while(unknown3()){
            x--;
            y--;
        }
        z=k+y;
    }
    //@ assert  a_1: x==y;
}
