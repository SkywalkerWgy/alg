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
    loop invariant i_0: x == y;

    loop invariant i_1: (w == 0) ==> (x % 2 == 0);

    loop invariant i_2: (w == 1) ==> (x % 2 == 1);

    loop invariant i_3: (z == 0) ==> (y % 2 == 1);

    loop invariant i_4: (z == 1) ==> (y % 2 == 0);


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
