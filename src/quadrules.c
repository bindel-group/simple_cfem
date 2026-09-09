#include <stdio.h>
#include <stdlib.h>

#include "quadrules.h"

double gauss_point(int i, int npts)
{
   static const double gauss_pts[] = {
        /* One point */
        0.0,

        /* Two points */
        -0.5773502691896257,
        0.5773502691896257,

        /* Three points */
        -0.7745966692414834,
        0.0,
        0.7745966692414834,

        /* Four points */
        -0.8611363115940526,
        -0.33998104358485626,
        0.33998104358485626,
        0.8611363115940526,

        /* Five points */
        -0.906179845938664,
        -0.538469310105683,
        0.0,
        0.538469310105683,
        0.906179845938664,

        /* Six points */
        -0.932469514203152,
        -0.661209386466265,
        -0.238619186083197,
        0.238619186083197,
        0.661209386466265,
        0.932469514203152,

        /* Seven points */
        -0.949107912342759,
        -0.741531185599394,
        -0.405845151377397,
        0.0,
        0.405845151377397,
        0.741531185599394,
        0.949107912342759,

        /* Eight points */
        -0.960289856497536,
        -0.796666477413627,
        -0.525532409916329,
        -0.183434642495650,
        0.183434642495650,
        0.525532409916329,
        0.796666477413627,
        0.960289856497536,

        /* Nine points */
        -0.968160239507626,
        -0.836031107326636,
        -0.613371432700590,
        -0.324253423403809,
        0.0,
        0.324253423403809,
        0.613371432700590,
        0.836031107326636,
        0.968160239507626,

        /* Ten points */
        -0.973906528517172,
        -0.865063366688985,
        -0.679409568299024,
        -0.433395394129247,
        -0.148874338981631,
        0.148874338981631,
        0.433395394129247,
        0.679409568299024,
        0.865063366688985,
        0.973906528517172,
    };

    return gauss_pts[( npts*(npts-1) )/2 + i];
}

double gauss_weight(int i, int npts)
{
   static const double gauss_wts[] = {
        /* One point */
        2.0,

        /* Two points */
        1.0,
        1.0,

        /* Three points */
        0.555555555555556,
        0.888888888888889,
        0.555555555555556,

        /* Four points */
        0.34785484513745384,
        0.65214515486254616,
        0.65214515486254616,
        0.34785484513745384,

        /* Five points */
        0.236926885056189,
        0.478628670499366,
        0.568888888888889,
        0.478628670499366,
        0.236926885056189,

        /* Six points */
        0.171324492379170,
        0.360761573048139,
        0.467913934572691,
        0.467913934572691,
        0.360761573048139,
        0.171324492379170,

        /* Seven points */
        0.129484966168870,
        0.279705391489277,
        0.381830050505119,
        0.417959183673469,
        0.381830050505119,
        0.279705391489277,
        0.129484966168870,

        /* Eight points */
        0.101228536290376,
        0.222381034453374,
        0.313706645877887,
        0.362683783378362,
        0.362683783378362,
        0.313706645877887,
        0.222381034453374,
        0.101228536290376,

        /* Nine points */
        0.081274388361574,
        0.180648160694857,
        0.260610696402935,
        0.312347077040003,
        0.330239355001260,
        0.312347077040003,
        0.260610696402935,
        0.180648160694857,
        0.081274388361574,

        /* Ten points */
        0.066671344308688,
        0.149451349150581,
        0.219086362515982,
        0.269266719309996,
        0.295524224714753,
        0.295524224714753,
        0.269266719309996,
        0.219086362515982,
        0.149451349150581,
        0.066671344308688,
    };

    return gauss_wts[( npts*(npts-1) )/2 + i];
}

//ldoc on
/**
 * ## Implementation
 */
/*static*/ int gauss2d_npoint1d(int npts)
{
    switch (npts) {
    case  1: return 1;
    case  4: return 2;
    case  9: return 3;
    case 16: return 4;
    case 25: return 5;
    default:
        fprintf(stderr, "%d quadrature points unsupported by rule\n", npts);
        exit(-1);
    }
}

void gauss2d_point(double* xi, int i, int npts)
{
    int d = gauss2d_npoint1d(npts);
    int ix = i%d, iy = i/d;
    xi[0] = gauss_point(ix, d);
    xi[1] = gauss_point(iy, d);
}

double gauss2d_weight(int i, int npts)
{
    int d = gauss2d_npoint1d(npts);
    int ix = i%d, iy = i/d;
    return gauss_weight(ix, d) * gauss_weight(iy, d);
}

/**
 * We only implement one triangle quadrature (the three-point Hughes rule).
 */
void hughes_point(double* xi, int i, int npts)
{
    switch (i) {
    case 0:
        xi[0] = 0.5;
        xi[1] = 0.0;
        return;
    case 1:
        xi[0] = 0.5;
        xi[1] = 0.5;
        return;
    case 2:
        xi[0] = 0.0;
        xi[1] = 0.5;
        return;
    default:
        fprintf(stderr, "Quadrature node index out of bounds\n");
        exit(-1);
    }
}

double hughes_weight(int i, int npts)
{
    return 1.0/6.0;
}

/**
 * ## Demonstration of Quadrature
 * 
 * The remainder of this file is not needed for FEM, but
 * serves as a self-contained demonstration for specification
 * and verification of Gauss-Legendre quadrature as a
 * floating-point C program.
 */

extern double cos(double);

double integrate (double (*f)(double), int n) {
  int i;
  double s = 0.0;
  for (i=0; i<n; i++)
    s = gauss_weight(i,n) * f(gauss_point(i,n)) + s;
  return s;
}

double testfun(double x) {
  return 0.5 * (1-x) * cos(x);
}

double integrate_testfun (void) {
  return integrate(&testfun, 2);
}
