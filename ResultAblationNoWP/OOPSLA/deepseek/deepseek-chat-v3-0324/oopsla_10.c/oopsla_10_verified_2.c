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
    loop invariant i_4: x == y;

    loop invariant i_5: (w == 0) <==> (x % 2 == 1);

    loop invariant i_6: (z == 1) <==> (y % 2 == 1);


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
