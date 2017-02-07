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

    def hecke_operator(self,p, k):
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
