#include <stdio.h>
#include <stdlib.h>

void binop_plus(double*, double*);

void main()
{
    double x[4]={10,20,1,2};
    double y[2];
    
    binop_plus(x, y);

    printf("X=");
    for(int i=0; i<4; i++)
        printf("\t%lf\n",x[i]);
    printf("Y=");
    for(int i=0; i<2; i++)
        printf("\t%lf\n",y[i]);

}
