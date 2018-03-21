#Called on a directory with appropriate names
# dir/space - the class of forms
# dir/p_k - the files that need to be put into space

import os
import sys
import pickle
import re

from sage.all_cmdline import *
from sage.rings.integer import Integer

load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("p_neighbor_internals.spyx")
load("algform.sage")

print "join_cluster %s"%(sys.argv[1])
dirname = sys.argv[1]
spacefile = dirname+"space"
spacefile_tmp = spacefile+".tmp"

def savespace(A):
    fout = open(spacefile_tmp, "w")
    fout.write(A.save())
    fout.close()
    os.rename(spacefile_tmp, spacefile)

def readmatrix(filname):
    fin = open(filname, "r")
    line=fin.readline()
    parts=line.split()
    m=int(parts[0])
    n=int(parts[1])
    if m!=n:
        print "Not square matrix\n"
        os.exit(1)
    M=Matrix(QQ, n, n, 0)
    for i in range(0, n):
        line=fin.readline()
        parts=line.split()
        for j in range(0, n):
            M[i,j]=int(parts[j])
    return M

initspace = open(spacefile, "r").read()
A = Algforms(s=initspace)

for filename in os.listdir(dirname):
    m =re.match('^([0-9]*)_([1,2])$', filename)
    if m:
        prime = int(m.group(1))
        k = int(m.group(2))
        mat = readmatrix(os.path.join(dirname,filename))
        A.hecke_ops[k][prime]=mat
        savespace(A)

        
