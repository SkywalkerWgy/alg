int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*@
    requires w == 1;
    requires z == 0;
    requires x == 0;
    requires y == 0;
    ensures e_1: x == y;
*/
void oopsla_06(int w, int z, int x, int y){
    /*@
        loop assigns z, w, x, y;
    */
    while(unknown1()) {

        /*@
            loop assigns x, y;
        */
        while(unknown2()){
            if(w%2 == 1) x++;
            if(z%2 == 0) y++;
        }
        z = x + y;
        w = z + 1;
    }
}
