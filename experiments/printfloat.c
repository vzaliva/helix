#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

/*
  Utility to print binary 64 or 32-bit representation of a floating
  point number.
*/
void main(int ac, char **av)
{
    int is_double;
    char *s;
    
    if(ac==3 && strcmp(av[1],"-d")==0)
    {
        is_double = 1;
        s = av[2];
    } else if (ac==2)
    {
        is_double = 0;
        s = av[1];
    } else
    {
        fprintf(stderr,"Usage: printfloat [-d] <number>\n");
        exit(1);
    }

    if(is_double)
    {
        double d;
        if(sscanf(s,"%lf",&d)!=1)
        {
            fprintf(stderr,"invalid number '%s'\n", s);
            exit(1);
        }
        uint64_t i = *((uint64_t *)&d);
        printf(("%lf = %" PRIu64 "\n"), d, i);
    } else
    {
        float f;
        if(sscanf(s,"%f",&f)!=1)
        {
            fprintf(stderr,"invalid number '%s'\n", s);
            exit(1);
        }
        uint32_t i = *((uint32_t *)&f);
        printf("%f = %" PRIu32 "\n", f, i);
    }
}
