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
        loop invariant i_46: z >= y - c;

        loop invariant i_47: z == k + y - c;

        loop invariant i_48: y <= k + z;

        loop invariant i_49: x <= z;

        loop invariant i_50: 0 <= x;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_52: z == k + y - c;

            loop invariant i_53: z >= y - c;

            loop invariant i_54: y <= k + z;

            loop invariant i_55: x <= z;

            loop invariant i_56: 0 <= x;

            loop invariant i_57: x == y;


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
            loop invariant i_51: x == y;


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
