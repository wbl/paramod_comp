def p_split(a, p):
    val = 0
    while mod(a, p)==0:
    	  a = a/p
	  val = val + 1
    return (a, val)

def quadratic_symbol(a, p):
    (aprime, val)=p_split(a, p)
    if mod(val, 2) == 1:
        return -1
    if mod(p, 2) == 0:
        if mod(aprime, 8)==1:
            return 1
        else:
            return -1
    else:
        return kronecker_symbol(aprime, p)

def nonsquare(p): #should make deterministic
    r=1
    while kronecker_symbol(r, p)!=-1:
         r = r+1
    return r

def gen_a(ndisc, cliff, p):
    if mod(p, 2) == 1:
        r=nonsquare(p)
        candidates = [1, r, p, p*r]
    else:
        candidates=[1,5,-1,-5, 2, 10, -2, -10]
    for c in candidates:
        if hilbert_symbol(c, -1*ndisc, p)==cliff:
            return c
    raise Exception('No possible candidates found')

def local_binary_form(disc, cliff, p):
    if cliff == 1:
        return [1, disc]
    else:
        (rdisc, val) = p_split(disc, p)
        val = mod(val, 2)
        ndisc=rdisc*(p**val)
        if Mod(p, 2) == 1:
           if  kronecker_symbol(-ndisc, p)==1:
               raise Exception ('Invalid combination of invariants')
        else:
            if Mod(-ndisc, 8)==7:
                raise Exception ('Invalid combination of invariants')
        a = gen_a(ndisc, cliff, p)
        return [a, ndisc/a]

def local_form(n, disc, cliff, p): #Doesn't work for p=2
    if n<2:
        Exception("n>3 required")
    if n==2:
        return local_binary_form(disc, cliff, p)
    else:
        a=1
        if quadratic_symbol(-1*a*disc, p)!=-1:
            a=p
        if quadratic_symbol(-1*a*disc, p)!=-1:
            Exception("Failure to pick a")
        cliff_inner = cliff*hilbert_symbol(a, a*disc, p)
        sub = local_form(n-1, a*disc, cliff_inner, p)
        sub.append(a)
        return sub

def squint(x):
    return QQ(x).numerator()*QQ(x).denominator()

def integralize(form):
    return [squint(x) for x in form]

def reduce_squares(form):
    return [squarefree_part(x) for x in form]

def form_with_local_invariants(n, disc, cliff, p):
    form = DiagonalQuadraticForm(ZZ,integralize(local_form(n, disc, cliff, p)))
    assert form.hasse_invariant(p)==cliff
    return form

def representable_padic_of_diagonal(form):
    form = DiagonalQuadraticForm(ZZ, form)
    n=form.dim()
    vec = [0 for x in range(0, n)]
    vec[0] = 1
    val = form(vec)
    return val

def prime_in_series(a, m):
    num = a
    while not(is_prime(num)):
        num += m
    return num

def crt_prime(problem):
    (base, modulus) = crt_solve(problem)
    return prime_in_series(base, modulus)

def crt_solve(problem):
    remainders = list()
    moduli = list()
    for (r, m) in problem:
        remainders.append(r)
        moduli.append(m)
    return (crt(remainders,moduli), prod(moduli))

def weak_square_approx(pairlist):
    '''Input: ordered pairs (t_p, p)
    Output: a rational t such that t is in the same square class as t_p
    at p, and not divisible by primes not in [p] or an auxiliary p_0'''
    # Two step algorithm: get the right valuation
    # then get the correct square class by picking p_0 with correct congruence
    # what about 2? A: residue mod 8+valuation matters
    t = 1
    for (tp,p) in pairlist:
        (pprimepart, val)=p_split(tp, p)
        t*=p**(val%2) #only need same square class
    corrector_problem = list()
    for (tp, p) in pairlist:
        (tpprime, val)=p_split(tp, p)
        (tprime, val)=p_split(t, p)
        if p==2:
            corrector_problem.append(((Mod(tpprime, 8)/Mod(tprime,8)).lift(), 8))
        else:
            corrector_problem.append(((Mod(tpprime, p)/Mod(tprime, p)).lift(),p))
    p_0=crt_prime(corrector_problem)
    t*=p_0
    return t
    
def generate_form(dimension, neg_places, determinant): #insert error checks
    if dimension == 2:
        P = neg_places + prime_factors(determinant)+[2]
        P = set(P)
        tprob= list()
        for p in P:
            cliff = 1
            if p in neg_places:
                cliff = -1
            f = local_binary_form(determinant, cliff, p)
            tprob.append((representable_padic(integralize(f)), p))
        t = weak_square_approx(tprob)
        form = [t, determinant/t]
        return integralize(form)
    else:
        P = neg_places + prime_factors(determinant)+[2]
        P = set(P)
        tprob = list()
        for p in P:
            cliff = 1
            if p in neg_places:
                cliff = -1
            f = local_form(dimension, determinant, cliff, p)
            tprob.append((representable_padic(integralize(f)), p))
        t = weak_square_approx(tprob)
        new_det = determinant*t
        new_neg = list()
        for p in P:
            if hilbert_symbol(t, new_det, p) == -1:
                if not(p in neg_places):
                    new_neg.append(p)
            else:
                if p in neg_places:
                    new_neg.append(p)
        form = generate_form(dimension-1, new_neg, new_det)
        form = [t] + form
        return reduce_squares(form)

def form_with_local_data(prime, expdimcliff):
    # expdim is list of triples (e_i, d_i, cliff)
    # indicating the local data
    # We do not handle 2. 2 sucks!
    form = list()
    for (exp, dim, cliff) in expdimcliff:
        if cliff == 1:
            part = [prime^exp]*dim
        else:
            part = [prime^exp]*(dim-1)
            append(part, prime^exp, nonsquare(prime))
        form += part
    return form
#open question: what representation of forms?
#want to end up with sage forms
#but they lack support for general basis changes iirc

#lots of choices about "arbitrarily close that are unclear here"

#Answer: QuadraticForm(M) and Hessian_matrix() undo each other
#and Hessian matrices just linear algebra (Is this right choice?)

#The algorithm requires "classically integral forms". And then primitivity
#enters the picture. This is what magma has?

def form_vec_reshape(form, vector):
    #extend vector to a basis, and carry out the variable substitution so
    #that the returned form has $f(1,0,0\ldots)=form(vector)
    pass

def complete_square(form, vector):
    m=form.Hessian_matrix()
    n=len(vector)
    for i in range(0,n):
        m[i,i]-=2*vector[i]^2
        for j in range(i+1, n):
            m[i,j]-=2*vector[i]*vector[j]
            m[j,i]-=2*vector[i]*vector[j]
    for i in range(0, n):
        assert(m[0,i]==0)
        assert(m[i, 0]==0)
    hessian=matrix(QQ, n-1,n-1)
    for i in range(0, n-1):
        for j in range(0, n-1):
            hessian[i, j]=m[i+1,j+1]
    return QuadraticForm(QQ, hessian)

def decomplete_square(form, vector):
    hessian=form.Hessian_matrix()
    n=len(vector)
    m=matrix(QQ, n, n)
    for i in range(0, n-1):
        for j in range(0, n-1):
            m[i+1, j+1]=hessian[i,j]
    for i in range(0,n):
        m[i,i]+=2*vector[i]^2
        for j in range(i+1, n):
            m[i,j]+=2*vector[i]*vector[j]
            m[j,i]+=2*vector[i]*vector[j]
    return QuadraticForm(QQ, m)

def completion_vector(form):
    hessian=form.Hessian_matrix()
    n=hessian.dimensions()[0]
    a=hessian[0,0]/2
    vec=vector(QQ, n)
    vec[0]=a
    for i in range(1, n):
        vec[i]=hessian[0][i]/(2*a)
    return vec

def iso_at_p(forma, formb, p):
    #Return locally integral
    #isomorphism between these forms by converting
    #both to canonical form and
    #recording the transformations that did so.
    pass

def approx_modulus(p, epsilon):
    k=1
    while 1/(p^k)>=epsilon:
        k=k+1
    return k

def approx_integer(data, epsilon):
    #data is a pair (n, p)
    residue=list()
    moduli=list()
    for (n, p) in data:
        residue.append(n)
        moduli.append(approx_modulus(p, epsilon))
    return crt(residue, moduli)

def approx_vector(data, epsilon):
    n=data[0][0].dimension()
    retval=vector(ZZ, n)
    for i in range(0,n):
        tdat=list()
        for (vec, p) in data:
            tdat.append((vec[i], p))
        retval[i]=approx_integer(tdat, epsilon)
    return retval

def approximate_primitive_data(data, epsilon):
    #each entry of data is a prime p and a vector of p-adic integers
    #such that the lowest valuation is 0
    #what is returned is a vector of relatively prime integers that approximates
    #each given vector to within epsilon
    n=data[0][0].dimension()
    retval=vector(ZZ, n)
    approx_problem=list()
    P=list()
    for (vec, p) in data:
        approx_problem.append(vec[0], p)
        P.append(p)
    retval[0]=approx_integer(approx_problem, epsilon)
    #next one is special
    Pstar=prime_factors(retval[0])
    Pstar=[p for p in Pstar if p not in P]
    residue=list()
    moduli=list()
    for (vec, p) in data:
        residue.append(vec[1], p)
        moduli.append(approx_modulus(p, epsilon))
    for p in Pstar:
        residue.append(1)
        moduli.append(p)
    retval[1]=crt(residue, moduli)
    for i in range(2, n):
        approx_problem=list()
        for(vec, p) in data:
            approx_problem.append(vec[i], p)
        retval[i]=approx_integer(approx_problem, epsilon)
    return retval

def appoximating_basis(data, epsilon):
    #compute a basis of Z that is within epsilon of the bases contained within data
    #for each prime, in the norm for Theorem 2.1
    n=data[0][0].dimensions()[0]
    retval=matrix(ZZ, n, n)
    for i in range(0, n):
        retval[i][i]=1
    for i in range(0, n):
        vecapprox_prob = list()
        intapprox_prob = list()
        for (bmat, p) in data:
            lvec=retval.solve_right(bmat[i])
            vecapprox=vector(QQ, i) #indexing translation/check correct on empty
            intapprox=vector(QQ, n-i)
            for j in range(0, i):
                vecapprox[j]=lvec[j]
    #TODO: what was I thinking: finish this function
    pass

def primative_exponent(vec):
    #returns b such that p^b*vec is primitive and in Z_p^n
    return max([-valuation(v,p) for  v in vec])

def act(M, T):
    return T.transpose()*M*T

def hensel_step(M, T, N, p, e):
    #If act(M,T)=N modulo p^e, return T' that does it modulo p^(e+1)
    #Note M should have determinant relatively prime to p
    #T'=T+p^eF
    M=M.change_ring(ZZ)
    T=T.change_ring(ZZ)
    N=N.change_ring(ZZ)
    D=(act(M,T)-N)/(p^e)
    #Now solve D=T^tMF+F^tMT for F, over p ?
    n=M.dimensions()[0]
    Dvec=Matrix(IntegerModRing(p), n^2, 1, lambda x,y: 0)
    Amat=Matrix(IntegerModRing(p), n^2, n^2, lambda x, y:0)
    #translate into linear algebra
    for i in range(0, n):
        for j in range (0,n):
            Dvec[i*n+j]=D[i,j]
    for i in range(0,n):
        for j in range(0,n):
            Tmat=Matrix(IntegerModRing(p), n, n, lambda x,y:0)
            Tmat[i,j]=1
            res=T.transpose()*M*Tmat+Tmat.transpose()*M*T
            for k in range(0,n):
                for l in range(0,n):
                    Amat[k*n+l, i*n+j]=res[k,l]
    Fvec=Amat.solve_right(Dvec)
    F=Matrix(IntegerModRing(p^(e+1)),n, n, lambda x,y:0)
    for i in range(0,n):
        for j in range(0,n):
             F[i,j]=Fvec[i*n+j,0]
    Tprime=T-p^e*F
    return Tprime

def find_minimal_entry(M, p):
    #from Sage source
    n=M.dimensions()[0]
    min_val=Infinity
    ij_index=None
    for d in range(n):
        for e in range(n-d):
            tmp_val=valuation(M[e, e+d], p)
            if tmp_val<min_val:
                ij_index=(e, e+d)
                min_val=tmp_val
    return ij_index

def p_adic_jordan(M, p):
    #Turns into something close to a jordan decompsition
    #Does so with exact rational quotients
    #Return the transformation matrix
    n=M.dimensions()[0]
    R=M.parent().base_ring()
    oldM=M
    tlist=list()
    if n==1:
        return Matrix(R, 1,1,[1]) #we are done
    if p!=2:
        (min_i, min_j)=find_minimal_entry(M, p)
        T=Matrix(R, n, n)
        T[0,min_i]=1
        T[min_i,0]=1
        if min_i != min_j:
            T[0,min_j]=1
        for d in range(n):
            if d!=0 and d!=min_i:
                T[d,d]=1   
        M=act(M, T)
        tlist.append(T)
        a=M[0,0]
        for j in range(1, n):
            b=M[0,j]
            g=GCD(a,b)
            T=Matrix(R, n, n)
            for k in range(0,n):
                T[k,k]=1
            T[j,j]= a/g
            T[0,j]=-b/g
            tlist.append(T)
            M=act(M, T)
        Tnew=prod(tlist)
        assert M==act(oldM, Tnew)
        Mnext=M.submatrix(1,1,n-1,n-1)
        Tmore=p_adic_jordan(Mnext, p)
        T=Matrix(R, 1,1, [1])
        T=T.block_sum(Tmore)
        tlist.append(T)
        Tnew=prod(tlist)
        return Tnew
    else:
        raise Exception("not implemented")
def p_adic_odd_split_hnorm(a,b,p, accuracy):
    #Return p-adic solution r,s to ar^2+bs^2=1
    #use hensel's lemma
    R=Qp(p, prec=accuracy, type='capped-rel')
    for r in range(1, p):
         if kronecker_symbol(((1-a*r^2)/b)%p, p)==1:
            s=sqrt(R((1-a*r^2)/b))
            break
    return(r,s)
        
def p_adic_odd_split(M, p, accuracy):
    #M is a 2x2 matrix whose quadratic form is ax^2+by^2
    #with a,b units in the p-adics
    #returns an p-adic integer matrix T such that act(M, T) has form x^2+aby^2
    #for p not 2. (In 2 case special things)
    R=Qp(p, prec=accuracy, type='capped-rel')
    T=Matrix(R, 2, 2)
    a=M[0,0]
    b=M[1,1]
    if quadratic_symbol(a, p)==1 or quadratic_symbol(b, p)==1:
        if quadratic_symbol(a,p)==1:
            T[0,0]=1/sqrt(R(a))
            T[1,1]=sqrt(R(a))
        else:
            T[0,0]=1/sqrt(R(b))
            T[1,1]=sqrt(R(b))
            T=Matrix(ZZ, 2, 2, [[0,1],[1,0]])*T
    else:
        (r,s)=p_adic_odd_split_hnorm(a,b, p, accuracy)
        T[0,0]=r
        T[1,0]=s
        #a*(r*x+s*b*y)^2+b*(s*x-r*a*y)^2
        T[0,1]=s*b
        T[1,1]=-r*a
    return T

def identity_n(n):
    if n<0:
        n=0
    M=Matrix(ZZ, n, n)
    for i in range(0, n):
        M[i,i]=1
    return M

def is_diagonal(M):
    n=M.dimensions()[0]
    for i in range(0, n):
        for j in range(i+1, n):
            if M[i,j]!=0:
                return false
    return true

def p_adic_canonical(M, p, accuracy):
    #return a T that makes M into cannonical form to within accuracy
    #first we exactly take jordan blocks
    #then we approximately normalize each individual block
    #in the case of 2 we have a lot more to do.
    R=Qp(p, prec=accuracy, type='capped-rel')
    M=Matrix(R, M)
    Mold=M
    if p!=2:
        tlist=list()
        tlist.append(p_adic_jordan(M, p))
        M=act(M,tlist[0])
        #Now we have to go down the main diagonal
        #if the next term has the same valuation, we need to push values down
        #onto it
        #if not we need to normalize by removing the square part
        n=M.dimensions()[0]
        for i in range(0,n-1):
            assert act(Mold, prod(tlist))==M
            assert is_diagonal(M)
            v=M[i,i]
            vn=M[i+1,i+1]
            (v1,a)=v.val_unit()
            (v2, b)=vn.val_unit()
            if v1==v2:
                Tsmall=p_adic_odd_split(Matrix(R, 2, 2, [[a, 0],[0,b]]),p, accuracy)
                T=identity_n(i).block_sum(Tsmall).block_sum(identity_n(n-i-2))
                tlist.append(T)
                M=act(M, T)
            else:
                #finish normalizing the ith block
                #the square classes are 1, r, p, rp
                #As we don't divide by p, only question is 1 or r
                #requires only non-p part
                if kronecker_symbol(a%p, p)==1:
                    T=identity_n(n)
                    T[i,i]=1/sqrt(R(a))
                else:
                    T=identity_n(n)
                    r=nonsquare(p)
                    T[i,i]=1/sqrt(R(a/r))
                T=Matrix(R, T)
                tlist.append(T)
                M=act(M, T)
        (_,a)=M[n-1,n-1].val_unit()
        if kronecker_symbol(a.residue(), p)==1:
            T=identity_n(n)
            T[n-1,n-1]=1/sqrt(R(a))
        else:
            T=identity_n(n)
            r=nonsquare(p)
            T[n-1,n-1]=1/sqrt(R(a/r))
        tlist.append(T)
        M=act(M, T)
    else:
        raise Exception("not implemented yet")
    T=prod(tlist)
    assert act(Mold, T)==M
    return prod(tlist)
def genus_form(rational, padiclist):
    #given the rational form, and a list of local forms to be isomorphic to
    #and some primes, return the integrally equivalent form
    pass

def integral_to_rational_invariants(invariant):
    pass

def genus_from_invariants():
    pass

