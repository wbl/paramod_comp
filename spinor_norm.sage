from sage.rings.integer import Integer

## port of spinor_norm.m
## We require pairs (M, Q) with Q a quadratic form and M a basis
## Q is represented so v*Q*v is the form. Not 2* it, the form

#TODO: use fact that gram matrix can half half-integral to make things
#easier

#when done, optimize for much better performance
def sqrfr_rat(num):
    num=QQ(num)
    return num.squarefree_part()

def quad_from_half_gram(M):
    return QuadraticForm(ZZ, Matrix(ZZ, 4*M))

def latauts(L, Q):
    g=L.transpose()*Q*L
    q=quad_from_half_gram(g)
    nlist=list()
    for x in q.automorphisms():
        Z=L*x*L^(-1)
        if Z.det()==1:
            nlist.append(sqrfr_rat(spinor_norm(Z, Q)))
        else:
            nlist.append(sqrfr_rat(spinor_norm(-1*Z, Q)))
    return nlist

def squarefree_prime_factors(x):
    factorization=factor(x)
    retval=list()
    for f in factorization:
        if f[1]%2==1:
            retval.append(f)
    return retval

def theta_equivalent(L1, L2, Q, nlist=None, theta_refine=True, g1=None, g2=None):
    #Determine if L1 and L2 are theta-equivalent lattices in Q
    #L1 and L2 have columns which are the basis of the lattices
    #TODO
    if g1 == None and not theta_refine:
        g1=Matrix(ZZ, 2*L1.transpose()*Q*L1)
    if g2 == None and not theta_refine:
        g2=Matrix(ZZ, 2*L2.transpose()*Q*L2)
    # Now we need to make these into quadratic forms 
    T=g1.__pari__().qfisom(g2.__pari__())
    if T==False:
        return False
    if not theta_refine:
        return True
    # Now convert T into an isometry
    #Note that Q*L1*T=Q*L2
    I=L1*T*L2^(-1)
    assert Q==I.transpose()*Q*I
    if I.determinant()==-1:
        I=-1*I
    norm=spinor_norm(I, Q)
    norm=QQ(norm)
    norm=norm.numerator()*norm.denominator()
    if nlist==None:
        nlist=list()
        auts=q1.automorphisms()
        for y in auts:
            assert q1(y)==q1
            assert q1(T)==q2
            x=T^(-1)*y*T
            assert q2(x)==q2
            Z=L2*x*L2^(-1)
            Y=L1*y*L1^(-1)
            assert Q==Z.transpose()*Q*Z
            assert Q==Y.transpose()*Q*Y
            test=QQ(spinor_norm(Z,Q)/spinor_norm(Y,Q))
            test=test.numerator()*test.denominator()
            assert is_square(test)
            if Z.det()==1:
                nlist.append(sqrfr_rat(spinor_norm(Z, Q)))
            else:
                nlist.append(sqrfr_rat(spinor_norm(-1*Z, Q)))
    #Now determine if norm is 1 when we tweak with elements of nlist
    fac_tot=reduce(lambda a, b: a.union(b), [set(prime_factors(x)) for x in nlist])
    fac_tot=list(fac_tot)
    dnorm=norm
    for x in fac_tot:
        while dnorm%x==0:
            dnorm=dnorm/x
    if dnorm.is_square()==False:
        return False
    norm=norm/dnorm
    fac_norm=squarefree_prime_factors(norm)
    for x in fac_norm:
        if x not in fac_tot:
            return False
    #Now need to do linear algebra over GF(2)
    nprimes=len(fac_tot)
    nops=len(nlist)
    operator=matrix(GF(2),nprimes, nops)
    vec=vector(GF(2), nprimes)
    for i in range(0, nprimes):
        if fac_tot[i] in fac_norm:
            vec[i]=1
            for j in range(0, nops):
                if nlist[j]%fac_tot[i]==0:
                    operator[i,j]=1
    if vec in operator.column_space():
        return True
    else:
        return False
#need p-neighbors to test

def quad_from_half_gram_rat(M):
    return QuadraticForm(QQ, Matrix(QQ, 4*M))

def vec_w_norm(Q, n):
    mat=Q.block_sum(Matrix(QQ, 1, 1, [-n]))
    sol=quad_from_half_gram_rat(mat).solve()
    vec=vector(QQ, sol[0:-1])/sol[-1]
    assert vec.dot_product(Q*vec)==n
    return vec

# What exactly do we need to do in the spinor op?
# What about 2?
def spinor_op(L,Q, p):
    N=L.transpose()*Q*L
    veca=vec_w_norm(N, 2*p)
    vecb=vec_w_norm(N, 2)
    transform=reflection(veca,N)*reflection(vecb, N)
    return L*transform

#Should this be here?
def p_spinor_one_neighbor(L, Q, p, v):
    L1=p_one_neighbor(L, Q, v, p)
    return spinor_op(L1, Q, p)

def p_spinor_neighbors(L, Q, p, k):
    ret=list()
    neighbors=p_neighbors(L, Q, p, k)
    for L1 in neighbors:
        if k%2==1:
            L2=spinor_op(L1, Q, p)
            ret.append(L2)
        else:
            ret.append(L1)
    return ret
