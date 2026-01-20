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
        loop invariant i_0: 0 <= i <= n;

        loop invariant i_1: -1 <= ret < n;

        loop invariant i_2: ret == -1 ==> (\forall integer j; 0 <= j < i ==> a[j] != key); loop invariant ret >= 0 ==> (0 <= ret < i && a[ret] == key);

        loop invariant i_3: ret >= 0 ==> (0 <= ret < i && a[ret] == key);

        loop invariant i_4: ret == -1 ==> (\forall integer j; 0 <= j < i ==> a[j] != key); loop invariant ret >= 0 ==> (0 <= ret < n && a[ret] == key);

        loop invariant i_5: ret >= 0 ==> (0 <= ret < n && a[ret] == key);


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