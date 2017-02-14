#enumerate isotropic subspaces mod p
#note questions about p=2

#for now massively simplify

def isotropic_lines(Q, p):
    '''Takes a form, not a lattice'''
    #TODO: more efficient+general method of Heine
    ret=list()
    #return a list of vectors v such that
    #v*Q*v==0 mod p
    #copypasta from sage source code
    n=Q.dimensions()[0]
    w=vector([ZZ(0) for i in range(n-1)]+[ZZ(1)])
    if n<=1:
        raise RuntimeError("Not implemented")
    nz=n-1
    while w[nz]==0:
        nz+=-1
    
    while True:
        if (w.dot_product(Q*w) % p == 0):
            ret.append(deepcopy(w))
        ## Look for the first non-maximal (non-normalized) entry
        ind = 0
        while (ind < nz) and (w[ind] == p-1):
            ind += 1
        ## Increment
        if (ind < nz):
            w[ind] += 1
            for j in range(ind):
                w[j] = 0
        else:
            for j in range(ind+1):    ## Clear all entries
                w[j] = 0

            if nz != 0:               ## Move the non-zero normalized index over by one, or return the zero vector
                w[nz-1] = 1
                nz += -1
        ## Test for zero vector
        if w == 0:
            return ret
        ## Test for p-divisibility

def isotropic_vector(Q, p):
    #We will want to live with Q that are smaller.
    #We will also never have to split something smaller then 3
    #so let's not
    #and p!=2
    n=Q.dimensions()[0]
    if n<=2:
        raise RuntimeError,"Not Implemented"
    else:
        v1=vector(ZZ, n)
        v2=vector(ZZ, n)
        v3=vector(ZZ, n)
        v1[0]=1
        v2[1]=1
        v3[2]=1
        nv1=(v1.dot_product(Q*v1)%p)
        if nv1==0:
            return v1
        v2=v2-((v2.dot_product(Q*v1)/nv1)%p)*v1
        nv2=v2.dot_product(Q*v2)%p
        if nv2==0:
            return v2
        v3=v3-((v3.dot_product(Q*v1)/nv1)%p)*v1
        v3=v3-((v3.dot_product(Q*v2)/nv2)%p)*v2
        nv3=v3.dot_product(Q*v3)%p
        if nv3==0:
            return v3
        assert v1.dot_product(Q*v2)%p==0
        assert v1.dot_product(Q*v3)%p==0
        assert v2.dot_product(Q*v3)%p==0
        a=0
        b=0
        done=false
        while not(done):
            a=randint(0, p-1)
            b=randint(0, p-1)
            vt=a*v1+b*v2
            gamma2=((-vt.dot_product(Q*vt)/nv3)%p)
            if kronecker_symbol(gamma2, p)==1:
                done=true
        gamma=sqrt(Mod(gamma2, p)).lift()
        ret=gamma*v3+vt
        assert ret.dot_product(Q*ret)%p==0
        return ret
    
def maximal_isotropic_splitting(L, Q, p):
    #Need to return an even number of vectors
    #such that they pair up nicely into planes
    nQ=L.transpose()*Q*L
    n=Q.dimensions()[0]
    basis=Matrix(QQ, n, n, 1)
    form=nQ
    k=(n-1)/2 #We'll ignore even for now
    xlist=list()
    zlist=list()
    for i in range(0,k):
        x=basis*isotropic_vector(form,p)
        for b in basis.columns():
            if x.dot_product(nQ*b) %p !=0:
                z=b
                break
        z=(1/z.dot_product(nQ*x)%p)*z
        z=z-((z.dot_product(nQ*z)/2)%p)*x
        xlist.append(x)
        zlist.append(z)
        assert z.dot_product(nQ*z)%p==0
        assert z.dot_product(nQ*x)%p==1
        #Now shrink form and reshape basis
        newbase=list()
        for b in basis.columns():
            b=b-(z.dot_product(nQ*b)%p)*x
            b=b-(x.dot_product(nQ*b)%p)*z
            newbase.append(b)
        basis=column_matrix(newbase)
        basis=basis.transpose().rref().transpose()
        basis=basis[:, 0:n-2]
        form=basis.transpose()*nQ*basis
    return (xlist, zlist)
    pass

def isotropic_spaces(L, Q, p, k):
    #For now just k=1
    if k !=1:
        raise RuntimeError, "Not implemented"
    else:
        lines=isotropic_lines(L.transpose()*Q*L, p)
        ret=list()
        for l in lines:
            mat=Matrix(QQ, len(l), 1)
            mat[:, 0]=l
            ret.append(mat)
        return ret

