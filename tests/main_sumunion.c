#include <stdio.h>
#include <stdlib.h>

void sumunion(double*, double*);

void main()
{
    double x[4]={10,20,1,2};
    double y[4];
    
    sumunion(x, y);

    for(int i=0; i<4; i++)
    {
        if(y[i]!=2*x[i])
        {
            printf("FAIL!\n");
            printf("X=");
            for(int j=0; j<4; j++)
                printf("\t%lf\n",x[j]);
            printf("Y=");
            for(int j=0; j<4; j++)
                printf("\t%lf\n",y[j]);
            exit(1);
        }
    }
    printf("PASS\n");
    exit(0);
}
