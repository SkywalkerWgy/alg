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
        loop invariant i_10: && z >= x && z <= k;

        loop invariant i_11: && x <= y && c <= k;

        loop invariant i_12: && y >= c && x >= 0;

        loop invariant i_13: && z % 2 == 1 || x == y;

        loop invariant i_14: && x == y || c % 2 == 0;

        loop invariant i_15: && z == k + y - c;

        loop invariant i_16: && x == y;

        loop invariant i_17: && x >= 0 && y >= 0;

        loop invariant i_18: && z == k + y;

        loop invariant i_19: && c == 0;

        loop invariant i_20: z >= x && z <= k;

        loop invariant i_21: x <= y && c <= k;

        loop invariant i_22: y >= c && x >= 0;

        loop invariant i_23: z % 2 == 1 && x == y;

        loop invariant i_24: z % 2 == 1 || x == y;

        loop invariant i_25: z % 2 == 1 && x == y && c % 2 == 0;

        loop invariant i_26: z % 2 == 1 && x == y && c == 0;

        loop invariant i_27: z == k + y && x == y && c == 0;

        loop invariant i_28: z == k + y - c && x == y && c == 0;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_30: z == k + y - c && x == y && c == 0;


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
            loop invariant i_29: z == k + y - c && x == y && c == 0;


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
