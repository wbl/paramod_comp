# usage: dimension.sage A
# prints dimension of A to stdout
import sys
import pickle
import os
from sage.rings.integer import Integer
load("algform.sage")

Afile = open(sys.argv[1], "rb")
savestr = Afile.read()
A=Algforms(s=savestr)
print A.dimension()
