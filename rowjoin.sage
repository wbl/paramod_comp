import os
import sys
import re
from sage.rings.integer import Integer

# Called on spacedir
# hunts operators and rows, puts together the rows for each operator
def readrow(filename):
    f = open(filename, "r")
    line = f.readline()
    parts = line.split()
    n = int(parts[0])
    v = vector(ZZ, n)
    line = f.readline()
    parts = line.split()
    for i in range(0, n):
        v[i] = int(parts[i])
    return v

print "rowjoin.py %s"%sys.argv[1]
dirname = sys.argv[1]

oplist = dict()
for filename in os.listdir(dirname):
    m = re.match("^([0-9]*)_([1,2])r([0-9]*)", filename)
    if m:
        prime = int(m.group(1))
        k = int(m.group(2))
        row = int(m.group(3))
        key = "%s_%s"%(str(prime), str(k))
        if key in oplist:
            oplist[key].append((dirname+filename, row))
        else:
            oplist[key]=list()
            oplist[key].append((dirname+filename, row))
# We now have gathered together the rows
for key in oplist:
    print key
    rowlist = oplist[key]
    dim = len(rowlist)
    op = Matrix(ZZ, dim, dim, 0)
    for entry in rowlist:
        filename = entry[0]
        row = entry[1]
        op[row] = readrow(filename)
    outfile = open(dirname+key+".tmp", "w")
    outfile.write("%s %s\n"%(dim, dim))
    for i in range(0, dim):
        for j in range(0, dim):
            outfile.write(str(op[i,j])+" ")
        outfile.write("\n")
    outfile.close()
    os.rename(dirname+key+".tmp", dirname+key)
