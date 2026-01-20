/*@ 
  requires n > 0;
  requires \valid(a + (0 .. n-1));
  ensures e_1: \result >= 0 ==> 0 <= \result < n && a[\result] == key;
  ensures e_2: \result < 0 ==> \forall integer j; 0 <= j < n ==> a[j] != key;
*/
int _linear_search(int a[], int n, int key) {
    int ret = -1;
    int i = 0;
    // Loop A
    /*@
        loop invariant i_0: n > 0;

        loop invariant i_1: \valid(a + (0 .. n-1));

        loop invariant i_2: 0 <= i <= n;

        loop invariant i_3: -1 <= ret < n;

        loop invariant i_4: ret >= 0 ==> a[ret] == key;

        loop invariant i_5: ret == -1 ==> \forall integer j; 0 <= j < i ==> a[j] != key;


        loop assigns i,ret;
   */
    while (ret == -1 && i < n){
        if (a[i] == key){ 
            ret = i; 
        }
        else { 
            i = i + 1; 
        }
    } 
  return ret;
}