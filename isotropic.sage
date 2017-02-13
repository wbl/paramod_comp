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

