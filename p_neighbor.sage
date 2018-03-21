#p-neighbors for lattices with basis
#This is based on Hein's Magma code, ported to sage+some things in sage
#for simple cases

#if we only cared about isomorphism we could use the Gram matrices
#and wouldn't have to care as much about the quadratic forms
#but we have to ensure our lattices use the same ambient quadratic space
#and so the construction gets more complicated
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ

def p_neighbors(L, Q, p, k):
    spaces=isotropic_spaces(L, Q, p,k)
    for space in spaces:
        X,Z=hyperbolic_complement(L, Q, space, p)
        X,Z,U=hensel_lift(L, Q, X, Z, p)
        for x2 in lifts_with_fixed_complement(L, Q, X, Z,p):
            L2=hermitize(L,Q, x2, Z, U, p)
            yield L2

