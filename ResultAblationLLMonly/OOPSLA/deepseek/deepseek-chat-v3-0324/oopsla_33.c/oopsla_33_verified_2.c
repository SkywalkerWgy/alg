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
        loop invariant i_0: z == k + y;

        loop invariant i_1: x >= 0;

        loop invariant i_2: y >= 0;

        loop invariant i_12: x >= y;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_3: y >= 0;

            loop invariant i_4: c >= 0;

            loop invariant i_5: x >= y;

            loop invariant i_6: z == k + y - c || z != k + y - c;

            loop invariant i_13: z == k + y - c;

            loop invariant i_14: x - y == \at(x - y, Loop_Entry) + 2 * (c - \at(c, Loop_Entry));


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
            loop invariant i_7: s for Loop C: ``` loop invariant x >= y;

            loop invariant i_8: x >= y;

            loop invariant i_9: y >= 0;

            loop invariant i_10: z == k + y;

            loop invariant i_11: x - y == \at(x - y, Loop_Entry);


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
