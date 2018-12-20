#include <stdio.h>
#include <stdlib.h>

void inductor(double*, double*);

void main()
{
    double x[1]={2};
    double y[1];
    
    inductor(x, y);
    
    if(y[0]!=256.)
    {
        printf("X=%lf\tY=%lf\n",x[0],y[0]);
        printf("FAIL!\n");
        exit(1);
    }
    printf("PASS\n");
    exit(0);
}
