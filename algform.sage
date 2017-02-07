class Algforms:
    def __init__(self, L, Q):
        self.latlist=list()
        self.latlist.append(L)
        self.autlist=list()
        self.autlist.append(latauts(L, Q))
        self.quad_form=Q
        self.hecke_ops=dict()
        n=Q.dimensions()[1]
        for i in range(1, floor(n/2)+1):
            self.hecke_ops[i]=dict()

    def hecke_operator(self,p, k):
        if k!=1:
            return RuntimeError, "Not impelmented"
        else:
            valid=True
            op=Matrix(ZZ, len(self.latlist), len(self.latlist))
            for i in range(0, len(self.latlist)):
                curlat=self.latlist[i]
                vecs=isotropic_lines(curlat.transpose()*Q*curlat, p)
                for v in vecs:
                    target=p_spinor_one_neighbor(curlat, Q, p, v)
                    found = False
                    for j in range(0, len(self.latlist)):
                        if theta_equivalent(self.latlist[j], target, Q, self.autlist[j]):
                            op[i,j]+=1
                            found = True
                            break
                    if not found:
                        self.latlist.append(target)
                        self.autlist.append(latauts(target, Q))
                        self.hecke_ops=dict()
                        n=Q.dimensions()[1]
                        for i in range(1, floor(n/2)+1):
                            self.hecke_ops[i]=dict()
                        op=Matrix(ZZ, len(self.latlist), len(self.latlist))
                        print "Need to expand list. Recompute all operators"
                        valid=False
            if valid:
                self.hecke_ops[1][p]=op
            return op
