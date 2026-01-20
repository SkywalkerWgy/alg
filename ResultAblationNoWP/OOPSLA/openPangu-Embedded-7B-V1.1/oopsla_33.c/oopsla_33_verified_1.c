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
        loop invariant i_0: x + y + c == z;

        loop invariant i_1: z == k + y - c;

        loop invariant i_2: 0 <= x && 0 <= y && 0 <= c;

        loop invariant i_3: x == y && c == 0;

        loop invariant i_4: z % 2 == x % 2;

        loop invariant i_5: z >= x && z >= y;

        loop invariant i_6: y >= c;

        loop invariant i_7: x >= 0 && y >= 0 && c >= 0;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_9: x == y && c == 0;


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
            loop invariant i_8: x == y && c == 0;


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
