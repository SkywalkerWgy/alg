int unknown1();
int unknown2();
int unknown3();
int unknown4();

void oopsla_10() {
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

// Loop A
  /*@
    loop invariant i_7: w || x == 0 || z == 0 || x == y;


    loop assigns z;
    loop assigns y;
    loop assigns x;
    loop assigns w;
  */
    while(unknown2()){
        if(w) {
            x++;
            w = !w;
        }
        
        if(!z) {
            y++; 
            z=!z;
        }
    }

  //@ assert a_1: x==y;
  
}
