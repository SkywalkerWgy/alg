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
        loop invariant i_31: 0 <= z && z == k + y;

        loop invariant i_32: 0 <= x && x == z - k + y;

        loop invariant i_33: 0 <= y && y == z - k - x;

        loop invariant i_34: z >= x - y - c;

        loop invariant i_35: c >= 0;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_39: 0 <= z && z == k + y;

            loop invariant i_40: 0 <= x && x == z - k + y;

            loop invariant i_41: 0 <= y && y == z - k - x;

            loop invariant i_42: z >= x - y - c;

            loop invariant i_43: c >= 0;

            loop invariant i_44: 0 <= x && x == z - k - y;

            loop invariant i_45: 0 <= c && c == k + y - x;


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
            loop invariant i_36: 0 <= x && x == z - k - y;

            loop invariant i_37: 0 <= y && y == z - k - x;

            loop invariant i_38: 0 <= c && c == k + y - x;


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
