#include <stdio.h>
#include <stdlib.h>
#include <time.h>

double D[3];
/* HELIX version */
void dynwin64(double *, double *);

/* SPIRAL version */
int dwmonitor(double  *X, double  *D)
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
    
    for(int i=0;i<10;i++)
    {
        unsigned char *p = x;
        for(int j=0; j<5*8; j++)
            *p++=rand();

        y[0]=0;
        dynwin64(x, y);

        int f = dwmonitor(x,D);
        
        printf("%d:\t%lf\t%d\n",i,y[0],f);
    }
}
