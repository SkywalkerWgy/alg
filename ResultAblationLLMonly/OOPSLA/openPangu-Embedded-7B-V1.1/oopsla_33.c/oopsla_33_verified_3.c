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
        loop invariant i_35: z == k - y - c;

        loop invariant i_36: x == y == c;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_43: z == k - y - c;

            loop invariant i_44: x == y == c;

            loop invariant i_45: x == k - y - z;

            loop invariant i_46: x == k - y - c;

            loop invariant i_47: y == k - x - c;

            loop invariant i_48: c == k - x - y;

            loop invariant i_49: x == k - y;

            loop invariant i_50: y == k - x;

            loop invariant i_51: c == k - x;

            loop invariant i_52: z == k - x;

            loop invariant i_53: y == k - c;

            loop invariant i_54: z == k - c;

            loop invariant i_55: x == k - z;

            loop invariant i_56: x == k - c;

            loop invariant i_57: y == k - z;

            loop invariant i_58: z == k - z;

            loop invariant i_59: x == k - y == c;

            loop invariant i_60: x == k - z == c;

            loop invariant i_61: x == k - c == y;

            loop invariant i_62: y == k - z == c;

            loop invariant i_63: y == k - c == x;

            loop invariant i_64: z == k - y == c;

            loop invariant i_65: z == k - z == c;

            loop invariant i_66: x == k - y == z;

            loop invariant i_67: x == k - c == z;

            loop invariant i_68: y == k - z == z;

            loop invariant i_69: z == k - c == z;

            loop invariant i_70: x == k - z == y;

            loop invariant i_71: y == k - z == x;

            loop invariant i_72: y == k - c == z;

            loop invariant i_73: z == k - z == x;

            loop invariant i_74: z == k - c == y;

            loop invariant i_75: x == k - z ==;


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
            loop invariant i_37: x == k - y - z;

            loop invariant i_38: x == k - y - c;

            loop invariant i_39: y == k - x - c;

            loop invariant i_40: c == k - x - y;

            loop invariant i_41: x == y == c;

            loop invariant i_42: z == k - y - c;


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
