import sys
import pickle
from sage.all_cmdline import *
from sage.rings.integer import Integer

load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("algform.sage")

fin_name=sys.argv[1]
fout_name=sys.argv[2]
fout_tmp_name=fout_name+".tmp"
#Read in the matrix
fin=open(fin_name, "r")
#What format? n m \n then n lines of m elements each
#ignore checkpoint for now
#and hardcode primes
line=fin.readline()
parts=line.split()
m=int(parts[0])
n=int(parts[1])
if m!=n:
    print "Not square matrix\n"
    os.Exit(1)
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
A=Algforms(L, M)
A.hecke_operator(3,1)
for p in primes(100):
    A.hecke_operator(p, 1)
    sA=A.save()
    fout=open(fout_tmp_name, "w")
    fout.write(sA)
    fout.close()
    os.rename(fout_tmp_name, fout_name)
    print p, "1"
for p in primes(20):
    A.hecke_operator(p, 2)
    sA=A.save()
    fout=open(fout_tmp_name, "w")
    fout.write(sA)
    fout.close()
    os.rename(fout_tmp_name, fout_name)
    print p, "2"




