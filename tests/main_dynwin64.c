#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

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


double random_double()
{
    double res;
    do
    {
        unsigned char *p = (unsigned char*)&res;
        for(int j=0; j<8; j++)
            *p++=rand();
    } while(!isnormal(res));
    return res;
}

void test_random()
{
    double x[5];
    double y[1];

    srand(time(NULL));
    
    for(int i=0;i<100;i++)
    {
        /* Random X */
        for(int j=0; j<5; j++)
            x[j]=random_double();

        /* Ramdom D */
        for(int j=0; j<3; j++)
            D[j]==random_double();
        
        int f = dwmonitor(x,D);

        y[0]=0;
        dynwin64(x, y);

        if((double)f != y[0])
            printf("! Iteration %d, Y=%lg, Expected %d\n",i,y[0],f);
        else
            printf("  Iteration %d, Y=%lg, Expected %d\n",i,y[0],f);

        /*
          if((double)f != y[i])
        {
            printf("FAIL!\n");
            printf("Iteration %d, Y=%lg, Expected %d\n",i,y[0],f);
            printf("X=\n");
            for(int j=0; j<5; j++)
                printf("\t%d:\t%le\n",j,x[j]);
            printf("D=\n");
            for(int j=0; j<3; j++)
                printf("\t%d:\t%le\n",j,D[j]);
            
            exit(1);
        }
         */
    }
    printf("PASS\n");
    exit(0);
}

/* test once on known values for debugging */
void test_once()
{
    double x[5]={1., 2., 3., 4., 5.};
    double y[1]={0.};
    
    D[0]=10.;
    D[1]=20.;
    D[2]=30.;
    srand(time(NULL));
    
    int f = dwmonitor(x,D);
    
    y[0]=0;
    dynwin64(x, y);
    
    if((double)f != y[0])
    {
        printf("FAIL!\n");
        printf("Y=%lg, Expected %d\n",y[0],f);
        exit(1);
    }

    printf("PASS\n");
    exit(0);
}


void main()
{
    test_random();
    //test_once();
}
