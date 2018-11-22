#include <stdio.h>
#include <stdlib.h>

void pointwise_plusD(double*, double*);
double D = 1000;

void main()
{
    double x[8];
    double y[8];
    for(int i=0; i<8; i++)
        x[i] = i+10;
    
    pointwise_plusD(x, y);
    
    for(int i=0; i<8; i++)
        printf("%d:\t%lf\t\%lf\n",i,x[i],y[i]);

}
