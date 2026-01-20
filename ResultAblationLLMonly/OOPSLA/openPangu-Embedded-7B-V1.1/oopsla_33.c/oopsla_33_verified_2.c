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
        loop invariant i_18: z >= x + y + c;

        loop invariant i_19: z == k + y - c;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_23: z == k + y - c;

            loop invariant i_24: x + y == k - z;

            loop invariant i_25: z >= x + y + c;

            loop invariant i_26: x >= 0 && y >= 0 && c >= 0;

            loop invariant i_27: y <= k && z >= x + y + c;

            loop invariant i_28: z <= k;

            loop invariant i_29: x <= k && y >= 0 && z <= k;

            loop invariant i_30: x <= k && y >= 0;

            loop invariant i_31: y <= k;

            loop invariant i_32: x + y + c == k - z;

            loop invariant i_33: y >= 0 && z <= k;

            loop invariant i_34: x <= k && y >= 0 && z;


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
            loop invariant i_20: x + y == k - z;

            loop invariant i_21: z == k + y - c;

            loop invariant i_22: z >= x + y + c;


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
