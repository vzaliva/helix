#include <stdio.h>
#include <stdlib.h>

void binop_plus(double*, double*);

void main()
{
    double x[4]={10,20,1,2};
    double y[2];
    
    binop_plus(x, y);

    for(int i=0; i<2; i++)
    {
        if(y[i]!=x[i]+x[i+2])
        {
            printf("FAIL!\n");
            printf("X=");
            for(int i=0; i<4; i++)
                printf("\t%lf\n",x[i]);
            printf("Y=");
            for(int i=0; i<2; i++)
                printf("\t%lf\n",y[i]);
            exit(1);
        }
    }
    printf("PASS\n");
    exit(0);
    

}
