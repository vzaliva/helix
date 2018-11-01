#include <stdio.h>
#include <stdlib.h>

extern double* dynwin(double (*f)(double), double*);

void main()
{
    double x[8];
    for(int i=0; i<8; i++)
        x[i] = i+10;
    
    double *y = amap(add_one, x);
    
    for(int i=0; i<8; i++)
        printf("%d:\t%lf\t\%lf\n",i,x[i],y[i]);

}
