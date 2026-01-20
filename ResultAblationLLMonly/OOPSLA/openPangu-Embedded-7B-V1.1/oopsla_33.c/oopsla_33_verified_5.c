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
        loop invariant i_84: z == k - y + c;

        loop invariant i_85: x == k - y;

        loop invariant i_86: z == k - y + c && 0 <= y <= k;

        loop invariant i_87: z == k - y + c && x == k - y;

        loop invariant i_88: x == k - y && y == z - k;


        loop assigns z, y, x;
    */
    while(unknown1()){
        int c = 0;
        // Loop B
        /*@
            loop invariant i_93: x == k - y && y == z - k && c == 0;


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
            loop invariant i_89: x + y == k - c;

            loop invariant i_90: y <= k && x + c == k - y;

            loop invariant i_91: x == k - y && y == z - k && 0 <= y <= k && c == 0;

            loop invariant i_92: z == k - y + c && 0 <= y <= k && y + c <= k && x == k - y;

            loop invariant i_94: x + y == k - c && y <= k && x >= 0 && c >= 0;

            loop invariant i_95: z == k - y + c && x == k - y && 0 <= y <= k && y + c <= k;


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
