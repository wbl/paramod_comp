#enumerate isotropic subspaces mod p

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
    #todo: there be bugs
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
        basis=Matrix(GF(p),column_matrix(newbase))
        basis=basis.transpose().rref().transpose()
        basis=basis[:, 0:n-2]
        basis=Matrix(ZZ, basis)
        form=basis.transpose()*nQ*basis
    return (xlist, zlist, Matrix(ZZ,basis).columns())

def pivot_list(n,k): #always assume 1 anisotropic vector
    if n<2*k:
        return list()
    if k==1:
        return [ [x] for x in range(0, n-1)]
    old_pivots=pivot_list(n-2, k-1)
    old_pivots=[ [x+1 for x in piv] for piv in old_pivots]
    pivots=[[0]+piv for piv in old_pivots]
    back_pivots=[piv+[n-2] for piv in old_pivots]
    pivots.extend(back_pivots)
    if 2*k<n-1:
        more=pivot_list(n-2, k)
        more=[ [x+1 for x in piv] for piv in more]
        pivots.extend(more)
    assert len(pivots)==binomial((n-1)/2, k)*2^k
    return pivots

def veciter_help(count, p):
    retlist=list()
    done=False
    vec=vector(ZZ, count)
    while not(done):
        retlist.append(copy(vec))
        pointer=count-1
        add=true
        while add and pointer>=0:
            vec[pointer]+=1
            add=False
            if vec[pointer]==p:
                vec[pointer]=0
                add=True
                pointer-=1
        if add:
            done=True
    return retlist

def all_zeros(mat):
    a=mat.dimensions()[0]
    b=mat.dimensions()[1]
    for i in range(0, a):
        for j in range(0, b):
            if mat[i,j]!=0:
                return False
    return True

def isotropic_spaces(L, Q, p, k):
    xlist, zlist, remainder=maximal_isotropic_splitting(L, Q, p)
    zlist.reverse()
    basis=column_matrix(xlist)
    basis=basis.augment(column_matrix(zlist))
    basis=basis.augment(column_matrix(remainder))
    n=basis.dimensions()[0]
    pivots=pivot_list(n,k)
    retlist=list()
    for pivot in pivots:
        #Need to compute all spaces that work
        #how?
        #Never underestimate the power of brute force!
        #First figure out how many coefficients we need
        #For once this is a row matrix saying how much of what
        #we need, for correspondence to Hein
        bmat=Matrix(ZZ, k, n, 0)
        count=0
        for i in range(0,k):
            #Add in the free entries on this row
            #they are after the pivot position
            #and not over smaller pivots
            count +=n-(pivot[i]+1)-(k-i-1)
        #Why yes we are iterating over (Z/p)^count
        for vec in veciter_help(count, p):
            pointer=0
            for i in range(0, k):
                for j in range(0, n):
                    if j<pivot[i]:
                        bmat[i, j]=0
                    elif j==pivot[i]:
                        bmat[i,j]=1
                    else:
                        if j in pivot[i+1:]:
                            bmat[i,j]=0
                        else:
                            bmat[i,j]=vec[pointer]
                            pointer+=1
            space=basis*bmat.transpose()
            nQ=L.transpose()*Q*L
            gram=space.transpose()*nQ*space%p
            if all_zeros(gram):
                retlist.append(space)
    return retlist

