# Create a space A, initalize it for a prime, compute the hecke operator for 3
# called p outname
import sys
import pickle
import os
from sage.all_cmdline import *
from sage.rings.integer import Integer

load("dubey_holenstein.sage")
load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("p_neighbor_internals.spyx")
load("algform.sage")

print "Generate %s %s"%(sys.argv[1], sys.argv[2])

def gen_genus_prime(prime):
    genus = list()
    M = Matrix(IntegerModRing(prime^2), 5, 5, 1)
    if prime % 8 in [3, 5]:
        M[3,3] = 2
        M[4,4] = prime
    else: 
        r = distinguished_nonsquare(prime)
        M[3,3] = 2*r
        M[4,4] = prime*r

    genus.append((prime, normal_form(M, prime^2)[1]))
    M = Matrix(IntegerModRing(16), 5, 5, 0)
    M[0, 1] = 1
    M[1, 0] = 1
    M[2, 3] = 1
    M[3, 2] = 1
    M[4, 4] = 2*prime

    genus.append((2, normal_form(M, 16)[1]))
    return genus

prime_str = sys.argv[1]
outname = sys.argv[2]

prime = int(prime_str)
form = form_from_genus(gen_genus_prime(prime))

form = Matrix(QQ, form)
form = 1/2*form
L = Matrix(QQ, 5, 5, 1)
A = Algforms(L=L, Q=form, theta=False)
A.initialize()
A.hecke_operator(3,1)

sA = A.save()
tmp_outname = sys.argv[2]+".tmp"
fh = open(tmp_outname, "w")
fh.write(sA)
fh.close()
os.rename(tmp_outname, outname)
