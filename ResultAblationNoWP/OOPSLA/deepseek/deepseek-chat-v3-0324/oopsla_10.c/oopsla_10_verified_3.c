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
    loop invariant i_7: x >= 0 && y >= 0 && (w == 0 || w == 1) && (z == 0 || z == 1);

    loop invariant i_8: x - y == w - z;

    loop invariant i_9: (w == 1 && x == y + 1) || (w == 0 && x == y);

    loop invariant i_10: (z == 1 && y == x + 1) || (z == 0 && y == x);


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
