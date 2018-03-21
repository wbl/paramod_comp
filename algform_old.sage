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
            targrow = i
            print "Using row ", targrow
            rowlist.append(targrow)
            curlat=self.latlist[targrow]
            if not self.theta:
                targets=p_neighbors(curlat, self.Q, p, k)
            else:
                targets=p_spinor_neighbors(curlat, self.Q, p, k)
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
    

class Eigenform:
    #Q: how to divide into Galois orbits?
    #Q: how to detect eisenstein series
    # let's look at root magnitudes?
    def __init__(self, space, vec, F=None):
        self.space=space
        F, newvec,_ = sage.rings.qqbar.number_field_elements_from_algebraics(vec)
        self.vec=vector(F, newvec)
        self.F = F

    def is_good(self, p):
        return not p.divides(self.space.determinant)

    def eigenvalue(self, p, k):
        op=self.space.hecke_operator(p, k)
        for i in range(0, len(self.vec)):
            if self.vec[i] !=0:
                return (op*self.vec)[i]/self.vec[i]

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

def simul_diag(ops):
    nops=len(ops)
    for i in range(0, nops):
        for j in range(i, nops):
            if ops[i]*ops[j]-ops[j]*ops[i] !=0:
                raise RuntimeError, "Noncommuting operators"
    n=ops[0].dimensions()[0]
    basis=Matrix(QQ, n, n,1)
    for op in ops:
        nop=basis^(-1)*op*basis
        D,P=nop.right_eigenmatrix()
        basis=P*basis
        done=True
        for i in range(0,n):
            for j in range(i+1, n):
                if D[i]==D[j]:
                    done=False
        if done:
            return basis.columns()
    print "Need more operators"
    return basis

