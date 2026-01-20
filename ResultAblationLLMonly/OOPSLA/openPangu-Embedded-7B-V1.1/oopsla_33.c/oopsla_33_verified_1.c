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
        loop invariant i_0: z >= x + y + c;

        loop invariant i_1: z == k + y + x;

        loop invariant i_2: x >= 0;

        loop invariant i_3: y >= 0;

        loop invariant i_4: c >= 0;

        loop invariant i_5: y >= x;

        loop invariant i_6: z == k + y;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_9: z >= x + y + c;

            loop invariant i_10: z == k + y + x;

            loop invariant i_11: x >= 0;

            loop invariant i_12: y >= 0;

            loop invariant i_13: c >= 0;

            loop invariant i_14: y >= x;

            loop invariant i_15: z == k + y;

            loop invariant i_16: x == y;

            loop invariant i_17: x >= 0 && y >= 0;


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
            loop invariant i_7: x == y;

            loop invariant i_8: x >= 0 && y >= 0;


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
