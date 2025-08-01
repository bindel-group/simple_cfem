#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include "vecmat.h"
#include "bandmat.h"
#include "mesh.h"
#include "assemble.h"
#include "element.h"
#include "fem.h"


// Set up the mesh on [0,1] with Dirichlet BC
fem_t* setup_test_mesh(int numelt, int degree, double u0, double u1)
{
    mesh_t* mesh = mesh_create1d(numelt, degree, 0.0, 1.0);
    fem_t* fe = malloc_fem(mesh, 1);
    int numnp = fe->mesh->numnp;
    fe->id[0]       = -1;
    fe->id[numnp-1] = -1;
    fe->U[0]        = u0;
    fe->U[numnp-1]  = u1;
    fem_assign_ids(fe);
    return fe;
}

void test_fem1(int d)
{
    fem_t* fe = setup_test_mesh(6, d, 0.0, 1.0);
    fe->etype = malloc_poisson_element();

    // Set up globals and assemble system
    double* R = malloc_vecmat(fe->nactive, 1);
    double* K = malloc_bandmat(fe->nactive, d);
    fem_assemble_band(fe, R, K);

    // Factor, solve, and update
    bandmat_factor(K);
    bandmat_solve(K, R);
    fem_update_U(fe, R);

    // Check linear interpolation
    for (int i = 0; i < fe->mesh->numnp; ++i)
        assert(fabs(fe->mesh->X[i]-fe->U[i]) < 1e-8);

    // Clean up
    free_vecmat(K);
    free_vecmat(R);
    free_element(fe->etype);
    free_fem(fe);
}

void rhs_const1(double* x, double* fx)
{
    *fx = 1.0;
}

void test_fem2(int d)
{
    fem_t* fe = setup_test_mesh(6, d, 0.0, 0.0);
    fe->etype = malloc_poisson_element();
    fem_set_load(fe, rhs_const1);

    // Set up globals and assemble system
    double* R = malloc_vecmat(fe->nactive, 1);
    double* K = malloc_bandmat(fe->nactive, d);
    fem_assemble_band(fe, R, K);

    // Factor, solve, and update
    bandmat_factor(K);
    bandmat_solve(K, R);
    fem_update_U(fe, R);

    // Solution should be exact (d > 1)
    for (int i = 0; i < fe->mesh->numnp; ++i) {
        double x = fe->mesh->X[i];
        double uref = x*(1-x)/2;
        assert(fabs(fe->U[i]-uref) < 1e-8);
    }

    // Clean up
    free_vecmat(K);
    free_vecmat(R);
    free_element(fe->etype);
    free_fem(fe);
}

int main()
{
    for (int d = 1; d <= 3; ++d)
        test_fem1(d);
    for (int d = 2; d <= 3; ++d)
        test_fem2(d);
    return 0;
}
