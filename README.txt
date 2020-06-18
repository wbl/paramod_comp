Code to compute quinary orthogonal modular forms.

Files:
- quinary_module_l.sage: Sage file with the functions to compute the quinary omfs.
- hypergeom.m: magma code to compute some hypergeometric motives.
- genera_squarefree_2-2000.sobj: Sage sobj file, it is a dictionary with keys the squarefree numbers
  in [2, 2000], for every D as before it has a list of quinary qf representative for every genus.

Example:
The following example shows how to compute de space of orthogonal modular forms
in the case of trivial weight (d = 1), and non trivial weight (d = 167) for a lattice of
discriminant 167.
In the trivial weight case we choose a one dimensional Hecke eigenfunction and 
compute some of the Tpk eigenvalues.
We do the same for the non trivial weight case.

sage: load('quinary_module_l.sage)
sage: quins = load('genera_squarefree_2-2000.sobj')
sage: qmod = quinary_module(quins[167][0])
sage: qmod.decompose(d = 1)
[Free module of degree 19 and rank 1 over Integer Ring
 Echelon basis matrix:
 [  1  10  60  20  30  30  60 120  30  20  30  10  60   5  20  10  30  30   5],
 Free module of degree 19 and rank 1 over Integer Ring
 Echelon basis matrix:
 [ 0  0  1 -1 -1  1  0 -1  0 -1 -1  0  2  1 -1  0  0  1  0],
 Free module of degree 19 and rank 2 over Integer Ring
 Echelon basis matrix:
 [ 0  0  1 -1  0 -1  0  0 -1  0  1  1  0  0  0  0  0  0  0]
 [ 0  0  0  0  1  1  0 -2 -1  1 -1  1  1 -1 -2  0  0  2  0],
 Free module of degree 19 and rank 15 over Integer Ring
 Echelon basis matrix:
 [ 1  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0 -1]
 [ 0  1  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0 -1]
 [ 0  0  1  1  0  0  0  0  0  0  1  0  2  0  0  0  0  0 -5]
 [ 0  0  0  2  0  0  0  0  0  0  0  1  6  0  0  0  0 -3 -6]
 [ 0  0  0  0  1  0  0  0  0  0  0  0  2  0  0  0  0 -1 -2]
 [ 0  0  0  0  0  1  0  0  0  0  1  0  0  0  0  0  0  0 -2]
 [ 0  0  0  0  0  0  1  0  0  0  0  0  0  0  0  0  0  0 -1]
 [ 0  0  0  0  0  0  0  2  0  0  0  0  0  0  1  0  0  2 -5]
 [ 0  0  0  0  0  0  0  0  1  0  1  0  0  0  0  0  0  1 -3]
 [ 0  0  0  0  0  0  0  0  0  1  0  0  3  0  1  0  0  0 -5]
 [ 0  0  0  0  0  0  0  0  0  0  3 -1  0  0  0  0  0  3 -5]
 [ 0  0  0  0  0  0  0  0  0  0  0  0 12 -1  0  0  0 -6 -5]
 [ 0  0  0  0  0  0  0  0  0  0  0  0  0  0  2  0  0  3 -5]
 [ 0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  1  0  0 -1]
 [ 0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  1  0 -1]]
sage: v = qmod.decompose()[1].0
sage: for p in primes(14):
....:     p, qmod.eigenvalue_tp_d(p, v, 1)
....:     
(2, -2)
(3, 0)
(5, -2)
(7, 2)
(11, -14)
(13, -34)
sage: for p in primes(6):
....:     p, qmod.eigenvalue_tp2_d(p, v, 1)
....:     
(2, 2)
(3, -17)
(5, 16)
sage: for p in primes(14):
....:     p, qmod.eigenvalue_tp_d(p, v, 167)
....:     
(2, -8)
(3, -10)
(5, -4)
(7, -14)
(11, -22)
(13, -4)
sage: for p in primes(6):
....:     p, qmod.eigenvalue_tp2_d(p, v, 167)
....:     
(2, 10)
(3, 11)
(5, -44)
