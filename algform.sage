import pickle
class Algforms:
    def __init__(self, L, Q):
        self.latlist=list()
        self.latlist.append(L)
        self.autlist=list()
        self.autlist.append(latauts(L, Q))
        self.Q=Q
        self.hecke_ops=dict()
        n=Q.dimensions()[1]
        for i in range(1, floor(n/2)+1):
            self.hecke_ops[i]=dict()

    def hecke_operator(self,p, k): #include more sanity checks
        if k in self.hecke_ops:
            if p in self.hecke_ops[k]:
                return self.hecke_ops[k][p]
        valid=True
        op=Matrix(ZZ, len(self.latlist), len(self.latlist))
        for i in range(0, len(self.latlist)):
            curlat=self.latlist[i]
            targets=p_spinor_neighbors(curlat, self.Q, p, k)
            for target in targets:
                found = False
                for j in range(0, len(self.latlist)):
                    if theta_equivalent(self.latlist[j], target, self.Q, self.autlist[j]):
                        op[i,j]+=1
                        found = True
                        break
                if not found:
                    self.latlist.append(target)
                    self.autlist.append(latauts(target, self.Q))
                    self.hecke_ops=dict()
                    n=self.Q.dimensions()[1]
                    for i in range(1, floor(n/2)+1):
                        self.hecke_ops[i]=dict()
                    op=Matrix(ZZ, len(self.latlist), len(self.latlist))
                    print "Need to expand list. Recompute all operators"
                    valid=False
        if valid:
            self.hecke_ops[k][p]=op
        return op
    
    def save(self):
        return pickle.dumps(self)

    def restore(self, s):
        tmp=pickle.loads(s)
        self.Q=tmp.Q
        self.latlist=tmp.latlist
        self.autlist=tmp.autlist
        self.hecke_ops=tmp.hecke_ops
        
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

class Eigenform:
    def __init__(self, space, vec):
        self.space=space
        self.vec=vec

    def eigenvalue(self, p, k):
        op=self.space.hecke_operator(p, k)
        for i in range(0, len(self.vec)):
            if self.vec[i] !=0:
                return (op*self.vec)[i]/self.vec[i]

    def euler_factor(self, p):
        pass

def simul_diag(ops):
    nops=len(ops)
    for i in range(0, nops):
        for j in range(i, nops):
            if ops[i]*ops[j]-ops[j]*ops[i] !=0:
                raise RuntimeError, "Noncommuting operators"
    n=ops[0].dimensions()[0]
    basis=Matrix(QQbar, n, n)
    for i in range(0, n):
        basis[i,i]=1
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

