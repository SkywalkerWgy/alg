int unknown1();
int unknown2();
int unknown3();

/*@
    requires z == k;
    requires x == 0;
    requires y == 0;
    requires c == 0;
    ensures  e_1: x == y;
*/
void oopsla_33(int k, int z, int x, int y, int c){
    /*@
        loop assigns z, y, x, c;
    */
    while(unknown1()){
        c = 0;
        /*@
            loop assigns y, x, c;
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
        /*@
            loop assigns x, y;
        */
        while(unknown3()){
            x--;
            y--;
        }
        z=k+y;
    }
}
