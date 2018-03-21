import sys
from sage.all_cmdline import *
from sage.rings.integer import Integer

load("dubey_holenstein.sage")
def write_form(filehandle, form):
    f = filehandle
    f.write("5 5")
    f.write("\n")
    for i in range(0, 5):
        for j in range(0,5):
            f.write(str(form[i,j])+" ")
        f.write("\n")
    f.close()

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
filename = sys.argv[2]

prime = int(prime_str) #Todo: error fixing
# Just does 5x5 paramodular right now
form = form_from_genus(gen_genus_prime(prime))

f = open(filename, "w+")

write_form(f, form)

