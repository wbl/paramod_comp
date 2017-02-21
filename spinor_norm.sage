## port of spinor_norm.m
## We require pairs (M, Q) with Q a quadratic form and M a basis
## Q is represented so v*Q*v is the form. Not 2* it, the form

#TODO: use fact that gram matrix can half half-integral to make things
#easier

#when done, optimize for much better performance

def reflection(v, Q):
    # Determine a matrix nxn for reflection by v with norm Q
    # Q will be the matrix v*Q*v is the form: so half-entries off diagonal
    n=Q.dimensions()[0]
    M=Matrix(QQ, n, n)
    norm=v.dot_product(Q*v)
    for i in range(0, n):
        q=vector(QQ, n)
        q[i]=1
        w=q-2*(q.dot_product(Q*v)/norm)*v
        M[:, i]=w
    return M

def norm(u,v,Q):
    return u.dot_product(Q*v)

def orthogonal_basis(Q):
    #ret.tranpose()*Q*ret is diagonal
    n=Q.dimensions()[0]
    M=Matrix(QQ, n, n)
    for i in range(0, n):
        M[i,i]=1
    for i in range(0, n):
        v=M.column(i)
        for j in range(0, i):
            v=v-norm(M.column(j), v, Q)*M.column(j)/norm(M.column(j), M.column(j), Q)
        for j in range(0,n):
            M[j, i]=v[j]
    return M

def spinor_norm(M, Q):
    # Compute the spinor norm of isometry M with norm Q
    n=Q.dimensions()[0]
    transform=M
    T=orthogonal_basis(Q)
    retval=1
    for i in range(0,n):
        vec=T.column(i)
        tmp=transform*vec-vec
        if tmp.dot_product(Q*tmp)!=0:
            transform=transform*reflection(tmp, Q)
            retval*=tmp.dot_product(Q*tmp)
    return retval

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

def theta_equivalent(L1, L2, Q, nlist=None):
    #Determine if L1 and L2 are theta-equivalent lattices in Q
    #L1 and L2 have columns which are the basis of the lattices
    #TODO
    g1=L1.transpose()*Q*L1
    g2=L2.transpose()*Q*L2
    # Now we need to make these into quadratic forms 
    q1=quad_from_half_gram(g1)
    q2=quad_from_half_gram(g2)
    assert q1.Gram_matrix()==2*g1
    assert q2.Gram_matrix()==2*g2
    T=q1.is_globally_equivalent_to(q2,return_matrix=True)
    if T==False:
        return False
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
            assert Q==Z.transpose()*Q*Z
            assert sqrfr_rat(spinor_norm(Z, Q))==sqrfr_rat(spinor_norm(I*Z*I^(-1), Q))
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
    fac_norm=prime_factors(norm)
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
    return vector(QQ, sol[0:-1])/sol[-1]

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
