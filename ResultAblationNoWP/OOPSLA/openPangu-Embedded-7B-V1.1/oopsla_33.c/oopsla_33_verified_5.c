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
        loop invariant i_58: z == k + y - c;

        loop invariant i_59: x == y;

        loop invariant i_60: z % 2 == 1;

        loop invariant i_61: y >= 0 && y <= k;

        loop invariant i_62: z >= 0 && z <= k;

        loop invariant i_63: c >= 0 && c <= k;

        loop invariant i_64: \forall int i; unknown1(i) && unknown2(i) && unknown3(i) ==> i >= 0 && i < k;

        loop invariant i_65: \exists int i; i >= 0 && i < k;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_66: z == k + y - c;

            loop invariant i_67: x == y;

            loop invariant i_68: z >= 0 && z <= k;

            loop invariant i_69: c >= 0 && c <= k;

            loop invariant i_70: \forall int i; unknown1(i) && unknown2(i) && unknown3(i) ==> i >= 0 && i < k;

            loop invariant i_71: \exists int i; i >= 0 && i < k;

            loop invariant i_72: y >= 0 && y <= k;


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
