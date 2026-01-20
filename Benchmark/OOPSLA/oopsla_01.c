int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * IC3 motivating example
 */ 

void oopsla_01(){
    int x = 1;
    int y = 1;
    /*@
        loop assigns y;
        loop assigns x;
    */
    while(unknown1()) {
        int t1 = x;
        int t2 = y;
        x = t1 + t2;
        y = t1 + t2;
    }
    //@ assert a_1: y >= 1;
}