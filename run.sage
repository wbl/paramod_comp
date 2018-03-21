import sys
import pickle
import os
import gc
from sage.all_cmdline import *
from sage.rings.integer import Integer

load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("p_neighbor_internals.spyx")
load("algform.sage")

fin_name=sys.argv[1]
fout_name=sys.argv[2]
fout_tmp_name=fout_name+".tmp"
#Read in the matrix
fin=open(fin_name, "r")
#What format? n m \n then n lines of m elements each
#ignore checkpoint for now
#and hardcode primes

# Wait, which form do I actually use here...?
line=fin.readline()
parts=line.split()
m=int(parts[0])
n=int(parts[1])
if m!=n:
    print "Not square matrix\n"
    sys.Exit(1)
M=Matrix(QQ, n, n, 0)
for i in range(0, n):
    line=fin.readline()
    parts=line.split()
    for j in range(0, n):
        M[i,j]=int(parts[j])
L=Matrix(QQ, n, n, 1)
M=1/2*M
print M
print L
# TODO: make restartable
A=Algforms(L=L, Q=M, theta=False)

initialized = False
if os.access(fout_name, os.R_OK):
    resin = open(fout_name, "rb")
    A.restore(resin.read())
    initialized=True
    resin.close()

if not initialized:
    A.initialize()

for p in primes(10):
    if p==2:
        next
    A.hecke_operator(p, 1)
    print gc.collect()
    sA=A.save()
    fout=open(fout_tmp_name, "w")
    fout.write(sA)
    fout.close()
    os.rename(fout_tmp_name, fout_name)
    print p, "1"
for p in primes(10):
    if p==2:
        next
    A.hecke_operator(p, 2)
    print gc.collect()
    sA=A.save()
    fout=open(fout_tmp_name, "w")
    fout.write(sA)
    fout.close()
    os.rename(fout_tmp_name, fout_name)
    print p, "2"
