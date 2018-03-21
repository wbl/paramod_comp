import pickle
import pdb

def quadmatred(M):
    u = M.LLL_gram()
    return u.transpose()*M*u

#TODO: better initialization
class Algforms:
    def __init__(self, s=None, L=None, Q=None, theta=True):
        if s == None:
            self.latlist=list()
            self.latlist.append(L)
            self.glist = list()
            self.glist.append(quadmatred(Matrix(ZZ, 2*L.transpose()*Q*L)))
            self.autlist=list()
            self.autlist.append(latauts(L, Q))
            self.Q=Q
            self.theta=theta
            self.hecke_ops=dict()
            det=(L.transpose()*Q*L).determinant()
            det=QQ(det)
            #Incorrect but we should fix somehow
            self.determinant=det.numerator()*det.denominator()
            n=Q.dimensions()[1]
            for i in range(1, floor(n/2)+1):
                self.hecke_ops[i]=dict()
        else:
            self.restore(s)

    def reconstruct(self, op, rowlist, bound):
        #The reconstruction step
        #TODO: accept noncontiguous list of rows, determine which will work
        # best ala Hein
        # Requires diagonalization?
        if not (1 in self.hecke_ops):
                return Matrix(ZZ, 0, 0), False
        if not (3 in self.hecke_ops[1]):
                return Matrix(ZZ, 0, 0), False
        print "Attempting reconstruction"
        # We'd like to throw in all constraints
        B=self.hecke_ops[1][3]
        n=B.dimensions()[0]
        #We solve for the symmetric matrix that commutes with B
        #and has the first r rows given by op[:, rows]
        #The input vector is size n^2. There are rn relations on rows,
        # n^2 on commutation, and n(n-1)/2 on symmetry, for
        #rn+n^2+n(n-1)/2 total relations.
        #We flatten matrices as m[i,j]=n*i+j
        d=len(rowlist)*n+n^2+n*(n-1)/2
        problem=Matrix(ZZ, len(rowlist)*n+n^2+n*(n-1)/2, n^2, 0)
        invec=vector(ZZ, ZZ(d))
        counter=0
        for i in range(0, len(rowlist)):
            for j in range(0, n):
                problem[counter,n*rowlist[i]+j]=1
                invec[counter]=op[rowlist[i],j]
                counter +=1
        assert counter==len(rowlist)*n
        for i in range(0, n):
            for j in range(0,n):
                mat=Matrix(ZZ, n, n, 0)
                mat[i, j]=1
                res=B*mat-mat*B
                for k in range(0, n):
                    for l in range(0,n):
                        problem[counter+n*k+l, n*i+j]=res[k,l]
        ourmax = 0
        for i in range(0, d):
            for j in range(0, n^2):
                if abs(problem[i,j])> ourmax:
                    ourmax = problem[i,j]
        limit = ourmax*bound*n^2+1
        mod = Primes().next(limit)
        print "Problem assembled with modulus %s and dimensions %s x %s"%( mod, d, n^2)
        modinvec = vector(GF(mod), invec)
        modproblem = Matrix(GF(mod), problem)
        #Can I accelerate this by removing redundancy
        try:
            outvec=modproblem.solve_right(modinvec)
            print "Found a solution"
        except ValueError as E:
            print "Failed reconstruction"
            return Matrix(ZZ, 0, 0), False
        if modproblem.right_nullity()!=0:
            print "Multiple reconstructions with rows", rowlist
            return Matrix(ZZ, 0, 0), False
        outop=Matrix(ZZ, n, n, 0)
        for i in range(0, n):
            for j in range(0,n):
                outop[i,j]=outvec[n*i+j].lift()
        return outop, True

    def initialize(self):
        done = False
        workqueue = list()
        workqueue.append(self.latlist[-1])
        while len(workqueue)>0:
            todo = workqueue.pop()
            neighbors = p_neighbors(todo, self.Q, 3, 1)
            for lat1 in neighbors:
                found = False
                for lat2 in self.latlist:
                    if theta_equivalent(lat1, lat2, self.Q, theta_refine=False):
                        found = True
                if not found:
                    self.latlist.append(lat1)
                    self.glist.append(quadmatred(Matrix(ZZ, 2*lat1.transpose()*self.Q*lat1)))
                    workqueue.append(lat1)
                
    def hecke_operator(self,p, k, fast=True, force=False, trace=False): #include more sanity checks
        #TODO: better way to report expansion?
        #Maybe compute hecke(3, 1) at init time?
        if self.determinant %p==0:
            return
        if k in self.hecke_ops:
            if p in self.hecke_ops[k]:
                if not force:
                    return self.hecke_ops[k][p]
        valid=True
        op=Matrix(ZZ, len(self.latlist), len(self.latlist))
        rowlist = list()
        for i in range(0, len(self.latlist)): #Replicate hein's logic here
            targrow = self.targrow_compute(i, rowlist, p)
            print "Using row ", targrow
            rowlist.append(targrow)
            curlat=self.latlist[targrow]
            if not self.theta:
                targets=p_neighbors(curlat, self.Q, p, k)
            else:
                targets=p_spinor_neighbors(curlat, self.Q, p, k)
            bound = 0
            for target in targets:
                tmat = Matrix(ZZ, 2*target.transpose()*self.Q*target)
                tmat = quadmatred(tmat)
                found = False
                for j in range(0, len(self.latlist)):
                    if theta_equivalent(self.latlist[j], target, self.Q, theta_refine=self.theta, g2=tmat, g1=self.glist[j]):
                        op[targrow,j]+=1
                        found = True
                        break
                if not found:
                    if trace:
                        print target
                        print self.latlist
                        print self.Q
                    self.latlist.append(target)
                    self.glist.append(tmat)
                    self.autlist.append(latauts(target, self.Q))
                    self.hecke_ops=dict()
                    n=self.Q.dimensions()[1]
                    for i in range(1, floor(n/2)+1):
                        self.hecke_ops[i]=dict()
                    op=Matrix(ZZ, len(self.latlist), len(self.latlist))
                    # Need better way to handle this issue
                    print "Need to expand list. Recompute all operators"
                    valid=False
                bound += 1
            if valid and fast:
                nOp, status=self.reconstruct(op, rowlist, bound)
                if status:
                    op=nOp
                    print "Reconstruction worked at", i+1
                    break
        if valid:
            self.hecke_ops[k][p]=op
            return op
        return False
    
    def save(self):
        return pickle.dumps(self)

    def restore(self, s):
        tmp=pickle.loads(s)
        self.Q=tmp.Q
        self.latlist=tmp.latlist
        self.autlist=tmp.autlist
        self.hecke_ops=tmp.hecke_ops
        self.theta = tmp.theta
        self.determinant = tmp.determinant
        try:
            self.glist = tmp.glist #This is problem if older code was used. Now in try catch: see if works. Need better regression tests. Philosophy question: do we need or should I just rerurn
        except AttributeError:
            self.glist = list()
            for l in self.latlist:
                self.glist.append(quadmatred(Matrix(ZZ, 2*l.transpose()*self.Q*l)))

    def eigenforms(self):
        operators=list()
        retval=list()
        for k in self.hecke_ops:
            for p in self.hecke_ops[k]:
                operators.append(self.hecke_ops[k][p])
        eigenvecs=simul_diag(operators)
        for vec in eigenvecs:
            retval.append(Eigenform(self, vec))
        return retval

    def has_operator(self, p, k):
        return p in self.hecke_ops[k]

    def targrow_compute(self, index, rowlist, p):
        #Todo: memoize value
        bound = len(self.latlist)
        target = index
        if self.has_operator(3, 1):
            op = Matrix(RDF,self.hecke_ops[1][3])
            _,eigvecs =  op.right_eigenmatrix()
            for i in range(0, eigvecs.dimensions()[0]):
                possible = True
                for j in range(0, eigvecs.dimensions()[1]):
                    for k in range(j+1, eigvecs.dimensions()[1]):
                        if eigvecs[i, j] == eigvecs[i,k]:
                            possible = False
                if possible:
                    target = i
                    break
        else:
            target = index
        if target in rowlist:
            for i in range(0, bound):
                if i not in rowlist:
                    target = i
                    break
        return target

class Eigenform:
    #Q: how to divide into Galois orbits?
    #Q: how to detect eisenstein series
    # let's look at root magnitudes?
    def __init__(self, space, vec, F=None):
        self.space=space
        self.vec=vec
        self.F = vec.base_ring()

    def is_good(self, p):
        return not p.divides(self.space.determinant)

    def eigenvalue(self, p, k):
        op=self.space.hecke_operator(p, k)
        for i in range(0, len(self.vec)):
            if self.vec[i] !=0:
                return (self.vec*op)[i]/self.vec[i]

    def coeff_field(self):
        return self.F

    def euler_factor(self, p):
        # We need to do more about missing values

        if self.space.has_operator(p,2) and self.space.has_operator(p,1):
            e1 = self.eigenvalue(p, 1)
            e2 = self.eigenvalue(p, 2)
            # Really we want something else
            F = self.coeff_field()
            R.<x> = PolynomialRing(F)
            return 1-e1*x+(p*e2+p^3+p)*x^2-e1*p^3*x^3+x^4*p^6
        elif self.space.has_operator(p, 1):
            e1 = self.eigenvalue(p, 1)
            F = self.coeff_field()
            R.<x> = PolynomialRing(F)
            return 1-e1*x
        else:
            return 1

    def is_SK(self):
        # Check that for 3 primes
        count = 0
        for p in [3, 5, 7, 11, 13]:
            if count == 3:
                break
            if self.space.has_operator(p, 1) and self.space.has_operator(p, 2):
                count += 1
                poly = self.euler_factor(p)
                field = self.coeff_field()
                R.<x> = PolynomialRing(field)
                q=(p*x-1)*(p^2*x-1)
                if not q.divides(poly):
                    return False
        return True

    def SK_lift_factors(self):
        pass

    def is_Yoshida(self): #Q how to test
        if self.is_SK():
            return False
        count = 0
        for p in [3,5,7,11,13]:
            if count == 3:
                break
            if self.space.has_operator(p, 1) and self.space.has_operator(p, 2):
                count+=1
                poly = self.euler_factor(p)
                poly = poly/poly[poly.degree()]
                if len(factor(poly))!=2:
                    return False
        return True

    def Yoshida_lift_factors(self):
        pass

def decompose(ops):
    irreducibles = list()
    spaces = list()
    n = ops[0].dimensions()[0]
    spaces.append(Matrix(QQ, n, n, 1).column_space())
    while len(spaces)>0:
        space = spaces.pop()
        decomp, done = split_or_irrep(space, ops)
        if done:
            irreducibles.append(decomp)
        else:
            spaces += decomp
    return irreducibles

def random_element(ops):
    n = ops[0].dimensions()[0]
    M=Matrix(QQ, n, n, 0)
    for op in ops:
        M += choice([-2,-1,0,1,2])*op
    return M

def split_or_irrep(V, ops):
    while 1:
        M = random_element(ops)
        M = M.restrict(V)
        potsplits = M.fcp()
        if len(potsplits)==1 and potsplits[0][1] == 1:
            return V, True
        else:
            result = list()
            for split in potsplits:
                poly = split[0]
                W = poly(M).left_kernel()
                if W.dimension() != 0 and W.dimension() != V.dimension():
                    result.append(W)
            if len(result) > 0:
                return result, False

def eigenvec(space, ops):
    M = Matrix(QQ, 1, 1, 0)
    while 1:
        M = random_element(ops)
        M = M.restrict(space)
        facts = M.fcp()
        if len(facts)==1 and facts[0][1] == 1:
            break
    print "Computing eigenvector on a space of dimension ", space.dimension()
    return Matrix(space.basis()).transpose()*Matrix(M.left_eigenspaces(format='galois')[0][1].basis()).transpose().columns()[0]

def simul_diag(ops):
    nops = len(ops)
    for i in range(0, nops):
        for j in range(i, nops):
            if ops[i]*ops[j] !=ops[j]*ops[i]:
                assert "Noncommuting operators"
    vecs = list()
    irreps = decompose(ops)
    for irr in irreps:
       vecs.append(eigenvec(irr, ops))
    return vecs
