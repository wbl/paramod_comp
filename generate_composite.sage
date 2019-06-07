import sys
from sage.all_cmdline import *
from sage.rings.integer import Integer

load("dubey_holenstein.sage")
load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("p_neighbor_internals.spyx")
load("algform.sage")

def write_form(filehandle, form):
    f = filehandle
    f.write("5 5")
    f.write("\n")
    for i in range(0, 5):
        for j in range(0,5):
            f.write(str(form[i,j])+" ")
        f.write("\n")
    f.close()

def gen_genus(num):
    genus = list()
    primes = prime_factors(num)
    if not len(primes) %2 == 1:
        assert False, "Need odd number of primes"
    for prime in primes:
        M = Matrix(IntegerModRing(prime^2), 5, 5, 1)
        if kronecker_symbol(2, num) == -1:
            M[3,3] = 2
            M[4,4] = num
        else:
            r = distinguished_nonsquare(prime)
            M[3,3] = 2*r
            M[4,4] = num*r
        genus.append((prime, normal_form(M, prime^2)[1]))
    M = Matrix(IntegerModRing(16), 5, 5, 0)
    M[0, 1] = 1
    M[1, 0] = 1
    M[2, 3] = 1
    M[3, 2] = 1
    M[4, 4] = 2*num
    genus.append((2, normal_form(M, 16)[1]))
    return genus

num_str = sys.argv[1]
filename = sys.argv[2]

num = int(num_str) #Todo: error fixing
# Just does 5x5 paramodular right now
form = form_from_genus(gen_genus(num))
form = Matrix(QQ, form)
form = 1/2*form
L = Matrix(QQ, 5, 5, 1)
A = Algforms(L=L, Q=form, theta=False)
A.initialize()
A.hecke_operator(3,1)

sA = A.save()
outname = sys.argv[2]
tmp_outname = sys.argv[2]+".tmp"
fh = open(tmp_outname, "w")
fh.write(sA)
fh.close()
os.rename(tmp_outname, outname)
