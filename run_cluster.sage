# Call A p k out
# Compute the operator for the space A that is p k and save it to outname
import sys
import pickle
import os
from sage.rings.integer import Integer

load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("p_neighbor_internals.spyx")
load("algform.sage")

print "run_cluster %s %s %s %s"%(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])

Afile = open(sys.argv[1], "rb")
p = int(sys.argv[2])
k = int(sys.argv[3])
if os.path.isfile(sys.argv[4]):
    print "Terminating early as no work required"
    sys.exit()
outfile = open(sys.argv[4]+".tmp", "w")
savestr = Afile.read()
A = Algforms(s=savestr)
op = A.hecke_operator(p, k)
if op==None:
    sys.exit(0)
n,m = op.dimensions()
outfile.write("%s %s\n"%(n, m))
for i in range(0, n):
    for j in range(0, m):
        outfile.write(str(op[i,j])+" ")
    outfile.write("\n")
outfile.close()
os.rename(sys.argv[4]+".tmp", sys.argv[4])

