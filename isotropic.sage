#enumerate isotropic subspaces mod p

def isotropic_vector(Q, p):
    #We will want to live with Q that are smaller.
    #We will also never have to split something smaller then 3
    #so let's not
    # We should make this derandomized?
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
        found = false
        for b in basis.columns():
            if x.dot_product(nQ*b) %p !=0:
                found=true
                z=b
                break
        if not(found):
            print x
            print basis
            print nQ
            print p
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
        basis=basis[:, 0:-2]
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
    done=False
    vec=vector(ZZ, count)
    while not(done):
        yield copy(vec)
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
            return

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
    nQ=L.transpose()*Q*L
    for pivot in pivots:
        retval = fast_pivotiter(pivot, basis, p, k, n, nQ)
        for thing in retval:
            yield thing


def isotropic_spaces_slow(L, Q, p, k):
    xlist, zlist, remainder=maximal_isotropic_splitting(L, Q, p)
    zlist.reverse()
    basis=column_matrix(xlist)
    basis=basis.augment(column_matrix(zlist))
    basis=basis.augment(column_matrix(remainder))
    n=basis.dimensions()[0]
    pivots=pivot_list(n,k)
    nQ=L.transpose()*Q*L
    for pivot in pivots:
        retval = pivotiter(pivot, basis, p, k, n, nQ)
        for ret in retval:
            yield retval
    

def pivotiter(pivot, basis, p, k, n, nQ):
    retlist = list()
    bmat=Matrix(ZZ, k, n, 0)
    count=0
    for i in range(0,k):
        #Add in the free entries on this row
        #they are after the pivot position
        #and not over smaller pivots
        count +=n-(pivot[i]+1)-(k-i-1)
        #Why yes we are iterating over (Z/p)^count
        #This is what we want to fix to make faster
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
        gram=space.transpose()*nQ*space%p
        if all_zeros(gram):
            yield space

def fast_pivotiter(pivot, basis, p, k, n, nQ):
    gram = basis.transpose()*nQ*basis %p
    R = PolynomialRing(GF(p), n*k, 'x', order='lex') # The parametrizing variables
    mat = Matrix(R, k,n, 0)
    gram = Matrix(GF(p), gram)
    for i in range(0, k):
        for j in range(0, n):
            mat[i, j]=R.gen(j*k+i)
    idlist = list()
    zeromat = mat*gram*mat.transpose()
    constcount = 0
    for i in range(0, k):
        for j in range(0, n):
            if j<pivot[i]:
                 idlist.append(R.gen(j*k+i))
                 constcount +=1
            elif j==pivot[i]:
                idlist.append(R.gen(j*k+i)-1)
                constcount +=1
            else:
                if j in pivot[i+1:]:
                    idlist.append(R.gen(j*k+i))
                    constcount +=1
    for i in range(0, k):
        for j in range(0, k):
            idlist.append(zeromat[i,j])
    constcount += k*(k+1)/2
    P = R.ideal(idlist)
    # We want to enumerate the solutions in the field of P
    # Some variables remain free, some are eliminated. How to get?
    # Also, how do we know this works?
    constraints = P.groebner_basis()
    if len(constraints) != constcount:
        if len(constraints) != 1:
            print "Problem"
            print pivot
            print constraints
            assert False
        return
    convar_list = [extract_linear(poly) for poly in constraints] #TODO: handle square root
    val_list = [-1/poly.coefficient(extract_linear(poly))*poly+extract_linear(poly) for poly in constraints]
    special = dict()
    for i in range(0, len(convar_list)):
        if convar_list[i].degree() == 2:
            assert val_list[i] == 0
            if len(convar_list[i].variables())==1:
                idlist.append(convar_list[i].variables()[0])
                special.update({convar_list[i].variables()[0]:0})
    P = R.ideal(idlist)
    constraints = P.groebner_basis()
    convar_list = [extract_linear(poly) for poly in constraints] #TODO: handle square root
    val_list = [-1/poly.coefficient(extract_linear(poly))*poly+extract_linear(poly) for poly in constraints]
    freevars = list()
    for x in R.gens():
        if x not in convar_list:
            freevars.append(x)
    convar_list += freevars
    val_list += freevars
    val_index = vector(ZZ, len(convar_list))
    for i in range(0, len(convar_list)):
        val_index[i] = R.gens().index(convar_list[i])
    assignments = enumerate_assigments(freevars, p, special)
    for assigment in assignments:
        tryvec = vector(GF(p), n*k)
        retmat = Matrix(ZZ, k, n, 0)
        for i in range(0, len(val_list)):
            tryvec[val_index[i]] = val_list[i].subs(assigment)
        for i in range(0, k):
            for j in range(0,n):
                retmat[i, j]=tryvec[j*k+i].lift()
        
        space = basis*retmat.transpose()
        if (space.transpose() *nQ*space) %p !=0:
            assert False
        yield space

def enumerate_assigments(freevars, p, special):
    dim = len(freevars)
    vecs = veciter_help(dim, p)
    for vec in vecs:
        sub = deepcopy(special)
        for i in range(0, dim):
            sub.update({freevars[i]:vec[i]})
        yield sub
        
    
def extract_linear(poly): #Problem: what if we extract the same thing twice.. ugh?
    # OK, the other problem is cancelling out the leading term
    terms = poly.monomials()
    for t in terms:
        if t.degree() == 1:
            return t
    return poly.lt()
