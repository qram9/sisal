#include "sisal_runtime.h"
#include <cstdio>
extern "C" sisal_array_t func_MAIN(int32_t);
int main(){
  // |Para(N)| = number of radicals (rooted ternary trees), OEIS A000598
  int exp[]={1,1,1,2,4,8,17,39};
  for(int n=0;n<=7;n++){
    sisal_array_t r=func_MAIN(n);
    printf("Para(%d).size=%d exp %d %s\n",n,(int)r.size,exp[n],(int)r.size==exp[n]?"OK":"FAIL");
  }
}
