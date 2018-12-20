#include <stdio.h>
#include <stdlib.h>
#include <time.h>

double D[3];
/* HELIX version */
void dynwin64(double *, double *);

/* SPIRAL version */
int dwmonitor(const double *X, const double *D)
{
    double q3, q4, s1, s4, s5, s6, s7, s8
            , w1;
    int w2;
    s5 = 0.0;
    s8 = X[0];
    s7 = 1.0;
    for(int i5 = 0; i5 <= 2; i5++) {
        s4 = (s7*D[i5]);
        s5 = (s5 + s4);
        s7 = (s7*s8);
    }
    s1 = 0.0;
    for(int i3 = 0; i3 <= 1; i3++) {
        q3 = X[(i3 + 1)];
        q4 = X[(3 + i3)];
        w1 = (q3 - q4);
        s6 = ((((w1 >= 0))) ? (w1) : (-(w1)));
        s1 = ((((s1 >= s6))) ? (s1) : (s6));
    }
    w2 = ((s1 >= s5));
    return w2;
}

void main()
{
    double x[5];
    double y[1];

    srand(time(NULL));
    
    for(int i=0;i<100;i++)
    {
        /* Random X */
        unsigned char *p = (unsigned char*)x;
        for(int j=0; j<5*8; j++)
            *p++=rand();

        /* Ramdom D */
        p = (unsigned char*)D;
        for(int j=0; j<3*8; j++)
            *p++=rand();
        
        int f = dwmonitor(x,D);

        y[0]=0;
        dynwin64(x, y);

        if((double)f != y[i])
        {
            printf("FAIL!\n");
            printf("Iteration %d, Y=%lf, Expected %d\n",i,y[i],f);
            printf("X=\n");
            for(int j=0; j<5; j++)
                printf("\t%d:\t%le\n",j,x[j]);
            printf("D=\n");
            for(int j=0; j<3; j++)
                printf("\t%d:\t%le\n",j,D[j]);
            
            exit(1);
        }
    }
    printf("PASS\n");
    exit(0);
}
