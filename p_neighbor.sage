#p-neighbors for lattices with basis
#This is based on Hein's Magma code, ported to sage+some things in sage
#for simple cases

#if we only cared about isomorphism we could use the Gram matrices
#and wouldn't have to care as much about the quadratic forms
#but we have to ensure our lattices use the same ambient quadratic space
#and so the construction gets more complicated
from sage.matrix.matrix import is_Matrix

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
    basis=Matrix(QQ, n, n, 1)
    Z=Matrix(ZZ, n, 0)
    for i in range(0, k):
        #Find a z[i] complementing x[i]
        x=X.column(i)
        found=False
        for v in basis.columns():
            if v.dot_product(nQ*X.column(i)) % p !=0:
                z=v
                found=True
                break
        if not(found):
            print "Failure to find thing in basis"
            print basis.transpose()*nQ*x %p
            assert False
        #adjust so that it has the right norms
        z=(1/z.dot_product(nQ*x)%p)*z
        assert z.dot_product(nQ*x) %p==1
        z=z-((z.dot_product(nQ*z)/2) %p)*x
        assert x.dot_product(nQ*x)%p == 0
        assert z.dot_product(nQ*x) %p == 1
        assert z.dot_product(nQ*z) %p == 0
        Z=Z.augment(colmat(z))
        #orthogonalize basis
        for j in range(0,basis.dimensions()[1]):
            b=basis.column(j)
            b=b-(b.dot_product(nQ*z)%p)*x
            b=b-(b.dot_product(nQ*x)%p)*z
            assert b.dot_product(nQ*z)%p==0
            assert b.dot_product(nQ*x)%p==0
            basis[:, j]=b
        for j in range(i+1, X.dimensions()[1]):
            xj=X.column(j)
            xj=xj-(xj.dot_product(nQ*z)%p)*x
            X[:, j]=xj
    check=X.transpose()*nQ*Z %p
    for i in range(0, k):
        for j in range(0,k):
            if i==j:
                assert check[i, j]==1
            else:
                assert check[i,j]==0
    return X,Z

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
        assert v.dot_product(nQ*v) %p^2==0
        for j in range(0, i):
            v=v-(xi.dot_product(nQ*X.column(j))%p^2)*Z.column(j)
            assert v.dot_product(nQ*v) %p^2==0
        X2.append(deepcopy(v))
    Z2=list()
    for i in range(0, k):
        zi=Z.column(i)
        assert zi.dot_product(nQ*zi) %p == 0
        v=zi-(zi.dot_product(nQ*zi)/2 %p^2)*X.column(i)
        assert v.dot_product(nQ*v) %p^2==0
        for j in range(0, i):
            v=v-(zi.dot_product(nQ*Z.column(j))% p^2)*X.column(j)
            assert v.dot_product(nQ*v) %p^2==0
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
        return list(Matrix(ZZ, 1, 1, 0))
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
    if k==1:
        Xlist.append(Xprime)
        return Xlist
    for m in Mlist:
        Xpp=Xprime+Zprime*p*m
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
    return L*1/(p)*outvecs

def p_neighbors(L, Q, p, k):
    ret=list()
    spaces=isotropic_spaces(L, Q, p,k)
    for space in spaces:
        X,Z=hyperbolic_complement(L, Q, space, p)
        X,Z,U=hensel_lift(L, Q, X, Z, p)
        for x2 in lifts_with_fixed_complement(L, Q, X, Z,p):
            L2=hermitize(L,Q, x2, Z, U, p)
            ret.append(L2)
    return ret
