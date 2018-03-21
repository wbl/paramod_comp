import sys
import json

load("spinor_norm_internals.spyx")
load("spinor_norm.sage")
load("isotropic.sage")
load("p_neighbor.sage")
load("p_neighbor_internals.spyx")
load("algform.sage")

print "analyze %s %s"%(sys.argv[1], sys.argv[2])

def jsonize_space(A):
    # We've got a bit of annoyance due to some creeping factors of two I need to understand
    # Conductor isn't easy to read off
    eigs = A.eigenforms()
    array = [ jsonize_eig(eig) for eig in eigs]
    datadict = dict()
    datadict['eigenforms'] = array
    datadict['dimension'] = len(eigs)
    return json.dumps(datadict, indent=4, sort_keys=True, separators ={': ', ', '})

def jsonize_eig(eig):
    field = eig.coeff_field()
    poly = ''
    if field.degree() == 1:
        poly = 'a-1'
    else:
        poly = field.defining_polynomial()
    data = dict()
    data['def_poly'] = str(poly)
    data['is_SK'] = eig.is_SK()
    data['is_Yoshida']=eig.is_Yoshida()
    plist = primes(100)
    euler_factors = dict()
    for p in plist:
        euler_factors[str(p)] = str(eig.euler_factor(p))
    data['euler_factors'] = euler_factors
    return data


fin_name = sys.argv[1]
fout_name = sys.argv[2]
fin = open(fin_name, "r")
A = Algforms(s=fin.read())
fout = open(fout_name, "w")
fout.write(jsonize_space(A))    
