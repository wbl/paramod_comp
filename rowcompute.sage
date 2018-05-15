# Call A p k row out
# Compute the row row of the operator for the space A that is p k and save it to outname

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

print "rowcompute %s %s %s %s %s"%(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])

Afile = open(sys.argv[1], "rb")
p = int(sys.argv[2])
k = int(sys.argv[3])
row = int(sys.argv[4])
if os.path.isfile(sys.argv[5]):
    print "Terminating early as no work required"
    sys.exit()
outfile = open(sys.argv[5]+".tmp", "w")
savestr = Afile.read()
A = Algforms(s=savestr)
row = A.compute_row(p,k, row)
n = len(row)
outfile.write("%s\n"%(len(row)))
for i in range(0, n):
    outfile.write(str(row[i])+" ")
outfile.write("\n")
outfile.close()
os.rename(sys.argv[5]+".tmp", sys.argv[5])
