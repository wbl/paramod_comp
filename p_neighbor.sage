#p-neighbors for lattices with basis
#This is based on Hein's Magma code, ported to sage+some things in sage
#for simple cases

#if we only cared about isomorphism we could use the Gram matrices
#and wouldn't have to care as much about the quadratic forms
#but we have to ensure our lattices use the same ambient quadratic space
#and so the construction gets more complicated
from sage.matrix.matrix import is_Matrix

def extend_to_primitive(A_input):
    """
    Given a matrix (resp. list of vectors), extend it to a square
    matrix (resp. list of vectors), such that its determinant is the
    gcd of its minors (i.e. extend the basis of a lattice to a
    "maximal" one in Z^n).

    Author(s): Gonzalo Tornaria and Jonathan Hanke.

    INPUT:
        a matrix, or a list of length n vectors (in the same space)

    OUTPUT:
        a square matrix, or a list of n vectors (resp.)

    EXAMPLES:
        sage: A = Matrix(ZZ, 3, 2, range(6))
        sage: extend_to_primitive(A)
        [ 0  1  0]
        [ 2  3  0]
        [ 4  5 -1]

        sage: extend_to_primitive([vector([1,2,3])])
        [(1, 2, 3), (0, 1, 0), (0, 0, 1)]

    """
    ## Deal with a list of vectors
    if not is_Matrix(A_input):
        A = matrix(A_input)      ## Make a matrix A with the given rows.
        vec_output_flag = True
    else:
        A = A_input
        vec_output_flag = False


    ## Arrange for A  to have more columns than rows.
    if A.is_square():
        return A
    if A.nrows() > A.ncols():
        return extend_to_primitive(A.transpose()).transpose()

    ## Setup
    k = A.nrows()
    n = A.ncols()
    R = A.base_ring()

    # Smith normal form transformation, assuming more columns than rows
    V = A.smith_form()[2]

    ## Extend the matrix in new coordinates, then switch back.
    B = A * V
    B_new = matrix(R, n-k, n)
    for i in range(n-k):
        B_new[i, n-i-1] = 1
    C = B.stack(B_new)
    D = C * V**(-1)

    ## DIAGNOSTIC
    #print "A = ", A, "\n"
    #print "B = ", B, "\n"
    #print "C = ", C, "\n"
    #print "D = ", D, "\n"

    # Normalize for a positive determinant
    if D.det() < 0:
        D.rescale_row(n-1, -1)

    ## Return the current information
    if  vec_output_flag:
        return D.rows()    
    else:
        return D

def colaug(v1, v2):
    n=v1.length()
    M=Matrix(ZZ, n,2)
    for i in range(0, n):
        M[i, 0]=v1[i]
        M[i, 1]=v2[i]
    return M

def p_one_neighbor(L, Q, v, p): #Make work for 2!
    n=L.dimensions()[0]
    v=L*v #Best done in column space
    for l in L.columns():
        if l.dot_product(Q*v) %p != 0: #TODO: check if rational
            w=l
            found=true
            break
    if not found:
        raise RuntimeError, "p divides everything"
    vw=w.dot_product(Q*v)
    s=v.dot_product(Q*v) #TODO: better way to write this
    if (s% p**2 !=0):
        a=(-s/(2*p*vw))%p
        v=v+p*a*w
        vw=w.dot_product(Q*v)
    assert v.dot_product(Q*v)% p**2 == 0
    nv=vector(ZZ, L.solve_right(v))
    nw=vector(ZZ, L.solve_right(w))
    M=extend_to_primitive(colaug(nv, nw))
    basis=L*M
    bv=basis.columns()[0]
    bw=basis.columns()[1]
    assert bv==v
    assert bw==w
    basis=basis.transpose()
    assert v.dot_product(Q*v)%p**2==0
    vw=w.dot_product(Q*v)%p
    for i in range(2, n):
        i_prod=(basis[i]*Q).dot_product(v)
        c=(i_prod/vw)%p
        basis[i]=basis[i]-c*w
    basis[0]=vector([x/p for x in basis[0]])
    basis[1]=basis[1]*p
    basis=basis.transpose()
    return basis

def p_neighbors(L, Q, p, k):
    """ Return all p_neighbors """
    pass
