#p-neighbors for lattices with basis
#This is based on Hein's Magma code, ported to sage+some things in sage
#for simple cases

#if we only cared about isomorphism we could use the Gram matrices
#and wouldn't have to care as much about the quadratic forms
#but we have to ensure our lattices use the same ambient quadratic space
#and so the construction gets more complicated
from sage.matrix.matrix import is_Matrix
import pdb

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

#todo: pythonize
def colmat(v):
    n=v.length()
    M=Matrix(QQ, n, 1)
    for i in range(0, n):
        M[i,0]=v[i]
    return M

def hyperbolic_complement(L, Q, X, p):
    #I feel sage really wants to use rows for spaces
    #Modified to return the basis we need 
    nQ=L.transpose()*Q*L
    k=X.dimensions()[1]
    n=X.dimensions()[0]
    basis=Matrix(QQ, n, n, 0)
    for i in range(0, n):
        basis[i,i]=1
    Z=Matrix(ZZ, n, 0)
    for i in range(0, k):
        #Find a z[i] complementing x[i]
        x=X.column(i)
        for v in basis.columns():
            if v.dot_product(nQ*X.column(i)) % p !=0:
                z=v
                break
        #adjust so that it has the right norms
        z=(1/z.dot_product(nQ*x)%p)*z
        z=z-((z.dot_product(nQ*z)/2) %p)*x
        assert x.dot_product(nQ*x)%p == 0
        assert z.dot_product(nQ*x) %p == 1
        assert z.dot_product(nQ*z) %p == 0
        Z=Z.augment(colmat(z))
        #orthogonalize basis
        for j in range(0, n):
            b=basis.column(j)
            b=b-b.dot_product(nQ*z)*x
            b=b-b.dot_product(nQ*x)*z
            basis[:, j]=b
    return Z

def hensel_lift(L, Q, X, Z, p):
    #First compute X_2
    #Then Z_2
    #Then Z_3
    #Return (X_2, Z_3)
    #These are lists of vectors(make matrix at end)
    k=X.dimensions()[1]
    n=X.dimensions()[0] #do I need it
    nQ=L.transpose()*Q*L
    X2=list()
    for i in range(0, k):
        xi=X.column(i)
        v=xi-(xi.dot_product(nQ*xi)/2%p^2)*Z.column(i)
        for j in range(0, i):
            v=v-xi.dot_product(nQ*X.column(j))*Z.column(j)
        X2.append(deepcopy(v))
    Z2=list()
    for i in range(0, k):
        zi=Z.column(i)
        v=zi-(zi.dot_product(nQ*zi)/2 %p^2)*X.column(i)
        for j in range(0, i):
            v=v-(zi.dot_product(nQ*Z.column(j))% p^2)*X.column(j)
        Z2.append(deepcopy(v))
    Z3=list()
    for i in range(0, k):
        v=Z2[i]
        for j in range(0, k):
            v+=((kronecker_delta(i,j)-X2[j].dot_product(nQ*Z2[i])) %p^2)*Z2[j]
        Z3.append(deepcopy(v))
    for v in X2:
        assert v.dot_product(nQ*v) %p^2==0
    for v in Z2:
        assert v.dot_product(nQ*v) %p^2==0
    basis=Matrix(QQ, n, n, 1)
    for j in range(0, n):
        b=basis.column(j)
        for i in range(0, k):
            b=b-(b.dot_product(nQ*Z3[i]) %p^2)*X2[i]
            b=b-(b.dot_product(nQ*X2[i]) %p^2)*Z3[i]
            basis[:, j]=b
    return (Matrix(X2).transpose(), Matrix(Z3).transpose(),basis)

def skew_symmetric_matrices(p, k):
    if k==1:
        return Matrix(ZZ, 1, 1, 0)
    L=list()
    coeffs=vector(ZZ, [0 for i in range(0, k*(k-1)/2)])
    while True:
        mat=Matrix(ZZ, k, k)
        for i in range(0, k):
            for j in range(0, i):
                idx=i*(i-1)/2+j
                mat[i,j]=coeffs[idx]%p
                mat[j, i]=(-mat[i,j])%p
        L.append(mat)
        ind=k*(k-1)/2-1
        add=True
        while add and ind>0:
            coeffs[ind]+=1
            if coeffs[ind]==p:
                add=True
                coeffs[ind]=0
            else:
                add=False
            ind-=1
        if add and ind==0:
            coeffs[0]+=1
            if coeffs[0]==p:
                return L

def lifts_with_fixed_complement(L, Q, Xprime, Zprime, p):
    #There is no code for this: have to read the theorem and
    #understand it.
    k=Zprime.dimensions()[1]
    Mlist=skew_symmetric_matrices(p, k)
    Xlist=list()
    for m in Mlist:
        Xpp=Xprime+Zprime*p*Mlist
        Xlist.append(Xpp)
    return Xlist

def hermitize(L, Q, X, Z, U, p):
    # Remember we need to take X, Z*p^2, U*p and p^3*basis
    # and then divide by p
    # p^2 basis is allowable as this is in X^#
    # Q: where does this get us the 1/p bits?
    # we also multiply by 2 for some convoluted reason
    n=L.dimensions()[1]
    neighbor=Matrix(ZZ, n, 0)
    neighbor=neighbor.augment(Matrix(ZZ, X))
    neighbor=neighbor.augment(Matrix(ZZ, p^2*Z))
    neighbor=neighbor.augment(Matrix(ZZ, p*U))
    neighbor=neighbor.augment(Matrix(ZZ, n, n, p^3))
    outvecs=neighbor.transpose().echelon_form().transpose()
    outvecs=Matrix(QQ, outvecs)[:, 0:n]
    return L*(1/p)*outvecs

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
    #TODO: woops
    #We need to ensure U is orthogonal mod p^2, not just p
    #(Actually understand proof more)
    #Then algorithm will work
    ret=list()
    spaces=isotropic_spaces(L, Q, p,k)
    for space in spaces:
        Z=hyperbolic_complement(L, Q, space, p)
        X,Z,U=hensel_lift(L, Q, space, Z, p)
        for x2 in lifts_with_fixed_complement(L, Q, X, Z,p):
            L2=hermitize(L,Q, x2, Z, U, p)
            ret.append(L2)
    return ret
