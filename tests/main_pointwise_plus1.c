#include <stdio.h>
#include <stdlib.h>

void pointwise_plus1(double*, double*);

void main()
{
    double x[8];
    double y[8];
    for(int i=0; i<8; i++)
        x[i] = i+10;
    
    pointwise_plus1(x, y);

    for(int i=0; i<8; i++)
    {
        if(y[i]!=x[i]+1)
        {
            printf("FAIL!\n");
            for(int i=0; i<8; i++)
                printf("%d:\t%lf\t\%lf\n",i,x[i],y[i]);
            exit(1);
        }
    }
    printf("PASS\n");
    exit(0);
}
