##########################################################
## cosas que hace mal sage                              ##
##                                                      ##
## 1. encontraba mal los vectores modulo 0 de una qf    ##
##    cambie el codigo para que devuelva el primer      ##
##    vector                                            ##
## 2. cache mal las series theta y devuelve la de otra  ##
##    delattr(_, '__theta_vec') para reiniciar eso      ##
##                                                      ##
##########################################################

from sage.quadratic_forms.quadratic_form import is_QuadraticForm as is_QF

###############################################################################
###############################################################################
########################### Dimension formulas ################################
###############################################################################
###############################################################################


def dimension_paramodular_3_prime(p):

  """
  Dimension of the space of paramodular forms of weight 3, level K(p), p prime.
  """

  if p <= 5:
    return 0
  dp = -1 + 1/2880*(p^2-1)
  dp+= 1/64*(p+1)*(1-kronecker(-1,p))
  dp+= 5/192  * (p-1) * (1+kronecker(-1,p))
  dp+= 1/72   * (p+1) * (1-kronecker(-3,p))
  dp+= 1/36   * (p-1) * (1+kronecker(-3,p))
  dp+= 1/5    * (1-kronecker(5,p))
  dp+= 1/8    * (1-kronecker(2,p))
  if p%12==5:
    dp+= 1/6
  return dp

def dimension_paramodular_3(N):

  """
  Dimension of the space of paramodular forms of weight 3, level K(N).
  """

  def leg(x, N):

      if x == -1 and N == 2:
        return 0
      elif x == -3 and N == 2:
        return -1
      elif x == 3 and N == 2:
        return 0
      elif N.is_prime():
        return kronecker(x, N)
      else:
        return prod([leg(x, p) for p in N.prime_divisors()])

  def NN(m, n):

      return len([p for p in N.prime_divisors() if p%n == m%n])
  
  Nps = N.prime_divisors()
  nNps = len(Nps)
  #H1
  ds = prod([p^2 + 1 for p in Nps])*6/2^7/3^3/5
  #H2
  ds-= 2^nNps*(11*(N%2 == 0)+14*(N%2 != 0))*2/2^8/3^2
  #H3
  ds+= 2^nNps*(5*(N%2 == 0)+2*(N%2 != 0))*2/2^6/3
  #H4
  ds+= 2^nNps*(5*(N%3 == 0)+(N%3 != 0))*3/2^3/3^3
  #H5
  ds+= 2^nNps/2^3/3^2
  #H6_1
  ds+= 3*(prod([p+leg(-1, p) for p in Nps])/2^5/3 + prod([p*leg(-1, p)+1 for p in Nps])/2^7/3)
  #H6_2
  ds-= prod([p+leg(-1, p) for p in Nps])/2^5/3 - prod([p*leg(-1, p)+1 for p in Nps])/2^7/3
  #H7_1
  ds+= 3*(prod([p+leg(-3, p) for p in Nps])/2^3/3^2 + prod([p*leg(-3, p)+1 for p in Nps])/2^3/3^3)
  #H7_2
  ds+= 0*(prod([p+leg(-3, p) for p in Nps])/2^3/3^2 - prod([p*leg(-3, p)+1 for p in Nps])/2^3/3^3)
  #H8
  ds-= 2^nNps/2^2/3
  #H9
  ds-= 2^nNps*((N%2 == 0) + 4*(N%2 != 0))/2^2/3^2
  #H10
  ds-= 2^(NN(1, 5) + NN(-1, 5))*((NN(2, 5) + NN(3, 5)) == 0)/5
  #H11
  ds-= 2^(NN(1, 8) + NN(-1, 8))*((NN(3, 8) + NN(5, 8)) == 0)/2^3
  #H12
  ds-= (prod([1+leg(3, p) for p in Nps])-prod([leg(-1, p) + leg(-3, p) for p in Nps]))/2^3/3
  #I1
  ds+= prod([p+1 for p in Nps])/2^3/3
  #I2
  ds-= 2^nNps/2^4/3
  #I3
  ds-= 2^nNps*N*3/2^5/3^2
  #I4
  ds-= 2^nNps*(4 - leg(-1, N))/2^5
  #I5
  ds+= 2^nNps*3/2^4/3
  #I6
  ds-= 2^nNps/2^3
  #I7
  ds-= 2^nNps*6/2^2/3^2
  #I8 ds+=0
  #I9
  ds-= prod([1+leg(-1, p) for p in Nps])/2^3
  #I10
  ds-= prod([1+leg(-3, p) for p in Nps])/2/3

  return ds + 1


def dimension_siegel_3(p):

  """
  Dimension of the space of siegel modular forms of weight 3 and level p?
  """

  if p <= 5:
    return 0
  ds = 1/2880 * (p+1)*(p^2+1)
  ds-= 7/576 * (p+1)^2
  ds+= 55/288 * (p+1)
  ds+= 1/36 * (p-23) * (1+kronecker(-3,p))
  ds+= 1/96 * (2*p-25) * (1+kronecker(-1,p))
  ds-= 1/12 * (1+kronecker(-1,p))*(1+kronecker(-3,p))
  if p%8 == 1:
    ds-= 1/2
  if p%8 == 7:
    ds-= 1/4
  if p%5 == 1:
    ds-= 4/5
  return ds

def dimension_plus_4(p):
  
  """
  Dimension of the plus space of modular forms of weight 4 and level p, p
prime.
  """

  if p <= 3:
    return 0
  else:
    return (p - 2 + kronecker(-1, p) + 2 * gp.qfbhclassno(4*p))/8

def dimension_minus_4(p):

  """
  Dimension of the minus space of modular forms of weight 4 and level p, p
prime.
  """

  if p <= 3:
    return 0
  else:
    return (p - 2 + kronecker(-1, p) - 2 * gp.qfbhclassno(4*p))/8


###############################################################################
###############################################################################
################################### Qfs #######################################
###############################################################################
###############################################################################

def thetaN(genus):

  N = 1
  S = set([Q.theta_series(N) for Q in genus])
  while len(S)<len(genus):
    N+= 1
    S = set([Q.theta_series(N) for Q in genus])
  return N

#######################################
#######################################
################ tp1 ##################
#######################################
#######################################

def qf_find_primitive_zeros_mod_p_regular(Q, p):

  """
  Given a quintic regular quadratic form over ZZ, and an odd prime p,
  returns the primitive zeros mod p of Q.
  """

  v1, v2, v3, v4, v5 = qf_basis(Q, p)
  yield primitivize(v1, p)
  for i in range(p):
    yield primitivize(i*v1+v2, p)
    yield primitivize(i*v1+v3, p)
    for j in range(p):
      yield primitivize((-i*j)*v1+i*v2+j*v3+v4, p)
      if j != 0:
        v = -Q(v5)*v1+i*j*v2+j^2*v4+j*v5
        yield primitivize(v, p)
      for k in range(1, p):
        v = i*k*v1 + (-Q(v5)-i*j)*v2 + k^2*v3 + j*k*v4 + k*v5
        yield primitivize(v, p)

def qf_find_primitive_zeros_mod_p_nonsingular(Q, p):

  """
  Given a quintic quadratic form over ZZ, and a prime p,
  returns the nonsingular primitive zeros mod p of Q.
  """

  if Q.disc()%p != 0 and p != 2:
    for v in qf_find_primitive_zeros_mod_p_regular(Q, p):
      yield v
  elif Q.disc()%p != 0 and p == 2:
    v = Q.find_primitive_p_divisible_vector__next(p)
    while v != None:
      yield v
      v = Q.find_primitive_p_divisible_vector__next(p, v)
  else:
    v = Q.find_primitive_p_divisible_vector__next(p)
    while v != None:
      if Q.is_zero_nonsingular(v, p):
        yield v
      v = Q.find_primitive_p_divisible_vector__next(p, v)

def qf_find_p_neighbors(Q, p, return_matrix = False):

  """
  Given a quintic quadratic form over ZZ, and a prime p,
  returns the p-neighbors of Q.
  """

  for v in qf_find_primitive_zeros_mod_p_nonsingular(Q, p):
    if return_matrix:
      Q1, M1 = Q.find_p_neighbor_from_vec(p, v, return_matrix = return_matrix)
      Q2, M2 = qf_reduction_pari(Q1, return_matrix = 1)
      yield Q2, M1*M2
    else:
      yield qf_reduction_pari(Q1)

def qf_find_genus(Q, p):

  genus = []
  L = [Q]
  while len(L) > 0:
    Qv = L[0]
    L = L[1:]
    is_in_genus = False
    for Qg in genus:
      if Qv.is_globally_equivalent_to(Qg):
        is_in_genus = True
    if not is_in_genus:
      genus.append(Qv)
      L+= qf_find_p_neighbors(Qv, p)
  return genus

### Cosas para calcular los tp2 ###

def primitivize(v, p):

  i = (v%p).nonzero_positions()[-1]
  v = (v*inverse_mod(v[i], p))%p
  return v

def primitivize2(v, p):

  i = (v%p).nonzero_positions()[-1]
  v = (v*inverse_mod(v[i], p^2))%p^2
  return v

def qf_orthogonal_random(Q, p, L):

  """
  Given a quadratic form over ZZ, a prime p and a list of vectors,
  returns a vector orthogonal to the vectors in L mod p.
  """

  M = matrix(GF(p), [Q.matrix()*v for v in L])
  K = M.right_kernel_matrix()
  n = K.nrows()
  while True:
    v = sum([randint(0, p-1)*K[i] for i in range(n)]).change_ring(ZZ)
    if (v%p) != 0:
      return primitivize(v, p)

def qf_hyperbolic_complement(Q, p, X):

  """
  Given a quintic quadratic form over ZZ, a prime p, Q.disc()%p != 0, and an isotropic
  plane mod p, returns another plane Z, such that
  <X[i], Z[j]> = delta_ij.
  """

  v1, v2 = X
  while True:
    v3 = qf_orthogonal_random(Q, p, [v1])
    if v2*Q.matrix()*v3%p != 0 and primitivize(v2, p)!=primitivize(v3, p):
      break
  v3 = v3*inverse_mod(v2*Q.matrix()*v3, p)%p
  v3 = (v3-Q(v3)*v2)%p
  while True:
    v4 = qf_orthogonal_random(Q, p, [v2, v3])
    if v1*Q.matrix()*v4%p != 0 and primitivize(v1, p) != primitivize(v4, p):
      break
  v4 = v4*inverse_mod(v4*Q.matrix()*v1, p)%p
  v4 = (v4-Q(v4)*v1)%p
  return [v4, v3]

def qf_hensel_lifting(Q, p, X, Z):

  """
  Given a quintic quadratic form over ZZ, a prime p, Q.disc()%p != 0, X, Z
  isotropic planes such that Z is hyperbolic complement of X. The function
  returns isotropic planes mod p^2 that are hyperbolic complement mod p^2.
  """

  x1, x2 = X
  z1, z2 = Z
  x1p = (x1 - Q(x1)*z1)%p^2
  x2p = (x2 - Q(x2)*z2 - x2*Q.matrix()*x1*z1)%p^2
  z1p = (z1 - Q(z1)*x1)%p^2
  z2p = (z2 - Q(z2)*x2 - z2*Q.matrix()*z1*x1)%p^2
  z1pp = (z1p + (1 - x1p*Q.matrix()*z1p)*z1p - x2p*Q.matrix()*z1p*z2p)%p^2
  z2pp = (z2p - x1p*Q.matrix()*z2p*z1p + (1 - x2p*Q.matrix()*z2p)*z2p)%p^2
  return [[x1p, x2p], [z1pp, z2pp]]


def qf_lifts_with_fixed_complement(Q, p, X, Z):

  """
  Given a quintic quadratic form Q, a prime p, Q.disc()%p != 0, X, Z isotropic planes
  mod p^2 such that Z is hyperbolic complement of X mod p^2. Returns the
  isotropic planes X' mod p^2 such that X=X' mod p, and X' and Z are hyperbolic
  complement mod p^2.
  """

  x1, x2 = X
  z1, z2 = Z
  for a in range(p):
      x1p = x1 + p*a*z2
      x2p = x2 - p*a*z1
      yield([x1p, x2p])

def qf_find_p2_neighbor_from_plane(Q, p, X, Z, return_matrix = False):

  X1 = [primitivize2(x, p) for x in X]
  Z1 = [primitivize(z, p) for z in Z]
  M = matrix(X1+Z1)
  while gcd(M.minors(4)) != 1:
      M[randint(0, 3), randint(0, 4)]+=p^2
      for i in range(4):
          M[i] = M[i]/gcd(M[i])
  M = extend_to_primitive(M)
  M[4] = M[4] - (M[4]*Q.matrix()*M[0])/(M[0]*Q.matrix()*M[2])%p*M[2] - (M[4]*Q.matrix()*M[1])/(M[1]*Q.matrix()*M[3])%p*M[3]
  M[0]/=p; M[1]/=p; M[2]*=p; M[3]*=p
  if return_matrix:
      Q1, M1 = qf_reduction_pari(Q(M.transpose()), return_matrix = True)
      return Q1, M.transpose()*M1
  else:
      return qf_reduction_pari(Q(M.transpose()))

def qf_isotropic_plane_random(Q, p):

  """
  Given a quintic quadratic form and a prime p returns an isotropic plane
  module p.
  """

  v1 = Q.find_primitive_p_divisible_vector__random(p)
  v1 = primitivize(v1, p)
  while True:
    v2 = qf_orthogonal_random(Q, p, [v1])
    if Q(v2)%p == 0 and v1 != v2:
      return [v1, v2]

def qf_basis(Q, p):

  """
  Given a quintic quadratic form and a prime p, returns a basis v_i of ZZ^5,
  such that: <v_i, v_j> = 1 iff i + j = 5, and 0 otherwise.
  """

  v1, v2 = qf_isotropic_plane_random(Q, p)
  v4, v3 = qf_hyperbolic_complement(Q, p, [v1, v2])
  v5 = qf_orthogonal_random(Q, p, [v1, v2, v3, v4])
  return [v1, v2, v3, v4, v5]

def qf_isotropic_planes(Q, p):

  """
  Given a quintic quadratic form and a prime p, Q.disc()%p != 0, returns the isotropic planes
  mod p.
  """

  v1, v2, v3, v4, v5 = qf_basis(Q, p)
  Qv5p = Q(v5)%p
  #pivot (3, 4)
  yield [v3, v4]
  for a in range(p):
    #pivot (2, 4)
    w1 = v2 - a^2*Qv5p*v3 + a*v5
    yield [w1%p, v4]
    for b in range(p):
      #pivot (1, 3)
      w1 = v1 + a*v2 - b^2*Qv5p*v4 + b*v5
      w2 = v3 - a*v4
      yield [w1%p, w2%p]
      for c in range(p):
        #pivot (1, 2)
        w1 = v1 - (2*a*c*Qv5p + b)*v3 - a^2*Qv5p*v4 + a*v5
        w2 = v2 - c^2*Qv5p*v3 + b*v4 + c*v5
        yield [w1%p, w2%p]

def qf_find_p2_neighbors(Q, p, return_matrix = False):

  if Q.disc()%p == 0 and (Q.disc()//p)%p != 0:
    Qr, Br = qf_quartic_from_quintic_deg(Q, p)
    r = Q.matrix().change_ring(GF(p)).kernel().0.change_ring(ZZ)
    for Xr in qf_quartic_isotropic_planes(Qr, p):
      x1, x2 = [x*Br for x in Xr]
      for a in range(p):
        for b in range(p):
          X = [x1 + a*r, x2 + b*r]
          Z = qf_hyperbolic_complement(Q, p, X)
          X1, Z1 = qf_hensel_lifting(Q, p, X, Z)
          for X2 in qf_lifts_with_fixed_complement(Q, p, X1, Z1):
            if return_matrix:
              yield qf_find_p2_neighbor_from_plane(Q, p, X2, Z, return_matrix = True)
            else:
              yield qf_find_p2_neighbor_from_plane(Q, p, X2, Z)
  else:
    for X in qf_isotropic_planes(Q, p):
      Z = qf_hyperbolic_complement(Q, p, X)
      X1, Z1 = qf_hensel_lifting(Q, p, X, Z)
      for X2 in qf_lifts_with_fixed_complement(Q, p, X1, Z1):
        if return_matrix:
          yield qf_find_p2_neighbor_from_plane(Q, p, X2, Z, return_matrix = True)
        else:
          yield qf_find_p2_neighbor_from_plane(Q, p, X2, Z)

def _qf_find_p2_neighbors_deg(Q, p, return_matrix = False):

    #TODO: falta escribir la parte de cuando Hasse_p(Q) = -1
    #en ese caso no tengo p2 vecinos
    Qr, Br = qf_quartic_from_quintic_deg(Q, p)
    for Xr in qf_quartic_isotropic_planes(Qr, p):
        Zr = qf_hyperbolic_complement(Qr, p, Xr)
        Xr1, Zr1 = qf_hensel_lifting(Qr, p, Xr, Zr)
        for Xr2 in qf_lifts_with_fixed_complement(Qr, p, Xr1, Zr1):
            X2 = [x*Br for x in Xr2]
            Z = [z*Br for z in Zr]
            if return_matrix:
                yield qf_find_p2_neighbor_from_plane(Q, p, X2, Z, return_matrix = True)
            else:
                yield qf_find_p2_neighbor_from_plane(Q, p, X2, Z)



##################################################
###### funciones para calcular Tp2 para p|D ######
##################################################

def qf_basis_deg(Q, p):
    """
    If p||D return a basis of V/V0.
    """

    M = Q.matrix().change_ring(GF(p))
    K = M.kernel()
    v = K.matrix()[0]
    V = v.parent()
    B = V.basis_matrix()
    i = 0
    while True and i < 5:
        M1 = copy(B)
        M1[i] = v
        if det(M1) != 0:
            break
        i+= 1
    Bd = list(B)
    Bd[i], Bd[4] = Bd[4], v
    return Bd

def qf_quartic_from_quintic_deg(Q, p):

    M = Q.matrix()
    B = qf_basis_deg(Q, p)
    M_B = matrix(ZZ, B[:4])
    return QuadraticForm(ZZ, M_B*M*M_B.transpose()), M_B

def qf_quartic_basis(Q, p):

    v1, v2 = qf_isotropic_plane_random(Q, p)
    v4, v3 = qf_hyperbolic_complement(Q, p, [v1, v2])
    return [v1, v2, v3, v4]

def qf_quartic_isotropic_planes(Q, p):

    v1, v2, v3, v4 = qf_quartic_basis(Q, p)
    #pivot (2, 4)
    yield [v2, v4]
    #pivot (3, 4)
    yield [v3, v4]
    for a in range(p):
        #pivot (1, 2)
        yield [(v1 + a*v3)%p, (v2 - a*v4)%p]
        #pivot (1, 3)
        yield [(v1 + a*v2)%p, (v3 - a*v4)%p]


def qf_isotropic_plane_random_deg(Q, p):

    Qr, Br = qf_quartic_from_quintic_deg(Q, p)
    v1, v2 = qf_isotropic_plane_random(Qr, p)
    return [v1, v2]


def qf_reduction_pari(Q, return_matrix = False):

    """
    Reduce the quadratic form using the implementation of LLL of pari.
    """

    M = pari.qflllgram(pari(Q)).sage()
    M*= M.det()
    if return_matrix:
        return Q(M), M
    else:
        return Q(M)

def qf_symmetry(Q, v):

  """
  Given a quintic quadratic form and a vector v, returns the matrix
  of the symmetry of v.
  """

  return identity_matrix(5) - v.column()*matrix(v)*Q.matrix()/Q.base_change_to(QQ)(v)

def qf_automorphism_symmetries_proper(Q, A):

  """
  Given a quintic quadratic form and a proper autometry A, returns the
  decomposition in symmetries of A.
  """

  if A == identity_matrix(QQ, 5):
    return []
  bs = (A - 1).columns()
  for b1 in bs:
    if b1 != 0:
      break
  A1 = qf_symmetry(Q, b1)*A
  bs = (A1 - 1).columns()
  for b2 in bs:
    if b2 != 0:
      break
  A1 = qf_symmetry(Q, b2)*A1
  if A1 == identity_matrix(QQ, 5):
    return [b1, b2]
  bs = (A1 - 1).columns()
  for b3 in bs:
    if b3 != 0:
      break
  A1 = qf_symmetry(Q, b3)*A1
  bs = (A1 - 1).columns()
  for b4 in bs:
    if b4 != 0:
      break
  return [b1, b2, b3, b4]

def qf_spin_norm(Q, A):

  """
  Given a quintic quadratic form Q, and an autometry A, returns the
  spin norm of A.
  """

  return prod([Q.base_change_to(QQ)(v) for v in qf_automorphism_symmetries_proper(Q, A)]).squarefree_part()



### Modulo de formas quinarias ###

def nu(d, n):

  """
  Given natural numbers d, and n returns the the character nu_d(n).
  The character is defined in primes p as nu_d(p) = -1 iff p|d.
  """
  
  return (-1)^len(gcd(d, n).prime_divisors())

def kron_ls(D, p_init):

  L = D.prime_divisors()
  L_aux = [vector([1 for p in L])]
  n = len(L)
  res = [1]
  l = 3
  while len(res) < 2^n:
    while (p_init*D)%l == 0:
      l = l.next_prime()
    kron_v = vector([kronecker(p, l) for p in L])
    if not kron_v in L_aux:
      L_aux.append(kron_v)
      res.append(l)
    l = l.next_prime()
  return res

def find_next_l(D, l):

  kron_l = vector([kronecker(p, l) for p in D.prime_divisors()])
  l2 = next_prime(l)
  while True:
    if D%l2 != 0:
      kron_l2 = vector([kronecker(p, l2) for p in D.prime_divisors()])
      if kron_l == kron_l2:
        break
    l2 = next_prime(l2)
  return l2



class quinary_module():

  def __init__(self, *args):

    self._thetaN = 10
    if is_QF(args[0]):
      self._Q = args[0]
      self._disc = self._Q.disc()
      self._tpinit = False
    else:
      Qs = args[0]
      self._Q = Qs[0]
      self._disc = Qs[0].disc()
      self._iso_dict = {}
      self._iso_dict_inv = {}
      self._iso_dict_theta = {}
      self._tpinit = True
      for i in range(len(Qs)):
        self._iso_dict[i] = Qs[i]
        self._iso_dict_inv[Qs[i]] = i
        thetaQ = Qs[i].theta_series(self._thetaN)
        if thetaQ in self._iso_dict_theta:
          self._iso_dict_theta[thetaQ].append(Qs[i])
        else:
          self._iso_dict_theta[thetaQ] = [Qs[i]]
    self.genus = []
    self._tps = {}
    self._tpsd = {}
    self._tp2s = {}
    self._tp2sd = {}
    self._eigen_tp = {}
    self._eigen_tp2 = {}
    self._charpols = {}
    self._ambiguous = {}
    self._not_ambiguous = {}
    self.PB = 6
    self.Q0 = self._Q
    #self.spins = [x for x in self._disc.divisors() if is_squarefree(x)]

  def disc(self):

    return self._disc
    
  def __repr__(self):

    return "Quinary module with genus represented by the form:\n"+self._Q.__repr__()
  
  def theta_kernel(self, p = 2):

    Tp = self.Tp_d(p, 1)
    h = len(self._iso_dict)
    vt = [self._iso_dict[i].theta_series(h) for i in range(h)]
    M = matrix(h, [vt[i][j] for i in range(h) for j in range(h)])
    return M.kernel()

  def theta_kernel_dimension(self):

    return self.theta_kernel().dimension()

  def _Tp_init(self, p):

    self._tpinit = True
    self._tp_init_p = p
    thetaN = self._thetaN
    Q = self._Q
    iso_dict = {0:Q}
    iso_dict_inv = {Q:0}
    iso_dict_theta = {Q.theta_by_pari(self._thetaN):[Q]}
    L = [Q]
    tp = {}
    Q_transformations = {Q:identity_matrix(5)}
    partial_mass = 0
    total_mass = Q.conway_mass()
    while L != []:
      R = L[0]; L = L[1:]
      partial_mass+= 1/R.number_of_automorphisms()
      i = iso_dict_inv[R]
      neighR = qf_find_p_neighbors(R, p, 1)
      for S, A in neighR:
        find_in_isos = False
        Stheta = S.theta_by_pari(thetaN)
        if Stheta in iso_dict_theta:
          for Qiso in iso_dict_theta[Stheta]:
            X = S.is_globally_equivalent_to(Qiso, 1)
            if not X == False:
              find_in_isos = True
              j = iso_dict_inv[Qiso]
              break
          if not find_in_isos:
            iso_dict_theta[Stheta].append(S)
            Q_transformations[S] = Q_transformations[R]*A
            j = len(iso_dict)
            iso_dict[len(iso_dict)] = S
            iso_dict_inv[S] = len(iso_dict_inv)
            L.append(S)
        else:
          j = len(iso_dict)
          Q_transformations[S] = Q_transformations[R]*A
          iso_dict_theta[Stheta] = [S]
          iso_dict[len(iso_dict)] = S
          iso_dict_inv[S] = len(iso_dict_inv)
          L.append(S)
        v = (i,j)
        if find_in_isos:
            X*= X.det()
        else:
            X = identity_matrix(5)
        s = qf_spin_norm(Q, Q_transformations[R]*A*X*Q_transformations[iso_dict[j]]^-1)
        if (i, j) in tp:
          if s in tp[(i,j)]:
            tp[(i,j)][s]+= 1
          else:
            tp[(i,j)][s] = 1
        else:
          tp[(i,j)] = {s:1}
    if partial_mass != total_mass:
      raise Exception('Missing forms in the genus')
    self._iso_dict_theta = iso_dict_theta
    self._iso_dict = iso_dict
    self._iso_dict_inv = iso_dict_inv
    self._tps = {p: tp}
    self._transformations = Q_transformations
    return tp

  def Tp(self, p):

    if not self._tpinit:
      return self._Tp_init(p)

    if p in self._tps:
      return self._tps[p]

    iso_dict = self._iso_dict
    iso_dict_theta = self._iso_dict_theta
    iso_dict_inv = self._iso_dict_inv
    g = len(iso_dict)
    tp = {(i, j):{} for i in range(g) for j in range(g)}
    for i in range(g):
      Q = iso_dict[i]
      neighQ = qf_find_p_neighbors(Q, p, 1)
      for R, A in neighQ:
        Rtheta = R.theta_series(self._thetaN)
        Rpossible_isos = iso_dict_theta[Rtheta]
        if len(Rpossible_isos) == 1:
          Qiso = Rpossible_isos[0]
          X = R.is_globally_equivalent_to(Qiso, 1)
          X*= X.det()
          j = iso_dict_inv[Qiso]
        else:
          for Qiso in Rpossible_isos:
            X = R.is_globally_equivalent_to(Qiso, 1)
            if not X == False:
              X*= X.det()
              j = iso_dict_inv[Qiso]
              break
        s = qf_spin_norm(self.Q0, self._transformations[Q]*A*X*self._transformations[Qiso]^-1)
        if s in tp[(i,j)]:
          tp[(i,j)][s]+= 1
        else:
          tp[(i,j)][s] = 1
    self._tps[p] = tp
    return tp

  def Tp_d(self, p, d):

      if p in self._tpsd:
          if d in self._tpsd[p]:
              return self._tpsd[p][d]
      tp = self.Tp(p)
      ncols = len(self._iso_dict)
      tpd = matrix(ncols)
      for (i, j) in tp:
          tpd[i, j] = sum([tp[(i,j)][k]*nu(d, k) for k in tp[(i,j)]])
      if d == 1 and d not in self._ambiguous:
          self._ambiguous[1] = []
          self._not_ambiguous[1] = list(range(ncols))
      if d in self._ambiguous:
          not_amb = self._not_ambiguous[d]
      else:
          amb = []
          not_amb = range(ncols)
          for i in self._iso_dict:
              R = self._iso_dict[i]
              for A in R.automorphisms():
                  if A.det() == 1:
                      s = qf_spin_norm(R, A)
                      if nu(d, s) == -1:
                          amb.append(i)
                          not_amb.remove(i)
                          break
          self._ambiguous[d] = amb
          self._not_ambiguous[d] = not_amb
      tpd = nu(d, p)*tpd[not_amb, not_amb]
      if self.disc()%p == 0 and (self.disc()//p)%p != 0:
         tpd+= nu(d, p)
      if p in self._tpsd:
          self._tpsd[p][d] = tpd
      else:
          self._tpsd[p] = {d:tpd}
      return tpd


  def Tp2(self, p):

    if not self._tpinit:
      return self._Tp_init(p)

    if p in self._tp2s:
      return self._tp2s[p]

    iso_dict = self._iso_dict
    iso_dict_theta = self._iso_dict_theta
    iso_dict_inv = self._iso_dict_inv
    g = len(iso_dict)
    tp2 = {(i, j):{} for i in range(g) for j in range(g)}
    for i in range(g):
      Q = iso_dict[i]
      neighQ = qf_find_p2_neighbors(Q, p, 1)
      for R, A in neighQ:
        Rtheta = R.theta_series(self._thetaN)
        Rpossible_isos = iso_dict_theta[Rtheta]
        if len(Rpossible_isos) == 1:
          Qiso = Rpossible_isos[0]
          X = R.is_globally_equivalent_to(Qiso, 1)
          X*= X.det()
          j = iso_dict_inv[Qiso]
        else:
          for Qiso in Rpossible_isos:
            X = R.is_globally_equivalent_to(Qiso, 1)
            if not X == False:
              X*= X.det()
              j = iso_dict_inv[Qiso]
              break
        s = qf_spin_norm(self.Q0, self._transformations[Q]*A*X*self._transformations[Qiso]^-1)
        if s in tp2[(i,j)]:
          tp2[(i,j)][s]+= 1
        else:
          tp2[(i,j)][s] = 1
    self._tp2s[p] = tp2
    return tp2

  def Tp2_d(self, p, d):

      if p in self._tp2sd:
          if d in self._tp2sd[p]:
              return self._tp2sd[p][d]
      tp2 = self.Tp2(p)
      ncols = len(self._iso_dict)
      tp2d = matrix(ncols)
      for (i, j) in tp2:
          tp2d[i, j] = sum([tp2[(i,j)][k]*nu(d, k) for k in tp2[(i,j)]])
      if d == 1 and d not in self._ambiguous:
          self._ambiguous[1] = []
          self._not_ambiguous[1] = list(range(ncols))
      if d in self._ambiguous:
          not_amb = self._not_ambiguous[d]
      else:
          amb = []
          not_amb = range(ncols)
          for i in self._iso_dict:
              R = self._iso_dict[i]
              for A in R.automorphisms():
                  if A.det() == 1:
                      s = qf_spin_norm(R, A)
                      if nu(d, s) == -1:
                          amb.append(i)
                          not_amb.remove(i)
                          break
          self._ambiguous[d] = amb
          self._not_ambiguous[d] = not_amb
      tp2d = tp2d[not_amb, not_amb]
      if p in self._tp2sd:
          self._tp2sd[p][d] = tp2d
      else:
          self._tp2sd[p] = {d:tp2d}
      return tp2d

  def eigenvalue_tp_d(self, p, v, d):

    if p in self._eigen_tp:
      if d in self._eigen_tp[p]:
        if v in self._eigen_tp[p][d]:
          return self._eigen_tp[p][d][v]
    g = len(v)
    not_amb = self._not_ambiguous[d]
    change = lambda j: not_amb.index(j)
    for i in range(g):
      if v[i] != 0:
        break
    Q = self._iso_dict[not_amb[i]]
    w = vector(ZZ, g)
    for R, A in qf_find_p_neighbors(Q, p, 1):
      Rtheta = R.theta_series(self._thetaN)
      Rpossibleisos = self._iso_dict_theta[Rtheta]
      if len(Rpossibleisos) == 1:
        Qiso = Rpossibleisos[0]
        j = self._iso_dict_inv[Qiso]
      else:
        for Qiso in Rpossibleisos:
          if Qiso.is_globally_equivalent_to(R):
            j = self._iso_dict_inv[Qiso]
            break
      if j in not_amb:
        X = R.is_globally_equivalent_to(Qiso, 1)
        X*= X.det()
        s = qf_spin_norm(self.Q0, self._transformations[Q]*A*X*self._transformations[Qiso]^-1)
        w[change(j)]+= nu(d, s)
    v_dual = vector([v[change(j)]*ZZ(self._iso_dict[j].number_of_automorphisms()) for j in range(len(self._iso_dict)) if j in not_amb])
    eigen = v_dual*w/v_dual[i]*nu(d, p)
    if self.disc()%p == 0 and (self.disc()//p)%p != 0:
        eigen+= nu(d, p)
    if p in self._eigen_tp:
      if d in self._eigen_tp[p]:
        self._eigen_tp[p][d][v] = eigen
      else:
        self._eigen_tp[p][d] = {v:eigen}
    else:
        self._eigen_tp[p] = {d:{v:eigen}}
    return eigen

  def eigenvalue_tp_1(self, p, v):

    d = 1
    if p in self._eigen_tp:
      if d in self._eigen_tp[p]:
        if v in self._eigen_tp[p][d]:
          return self._eigen_tp[p][d][v]
    g = len(v)
    not_amb = self._not_ambiguous[l]
    change = lambda j: not_amb.index(j)
    for i in range(g):
      if v[i] != 0:
        break
    Q = self._iso_dict[not_amb[i]]
    w = vector(ZZ, g)
    for R in qf_find_p_neighbors(Q, p, 0):
      Rtheta = R.theta_series(self._thetaN)
      Rpossibleisos = self._iso_dict_theta[Rtheta]
      if len(Rpossibleisos) == 1:
        Qiso = Rpossibleisos[0]
        j = self._iso_dict_inv[Qiso]
      else:
        for Qiso in Rpossibleisos:
          if Qiso.is_globally_equivalent_to(R):
            j = self._iso_dict_inv[Qiso]
            break
      if j in not_amb:
        w[change(j)]+= 1
    v_dual = vector([v[change(j)]*ZZ(self._iso_dict[j].number_of_automorphisms()) for j in range(len(self._iso_dict)) if j in not_amb])
    if self.disc()%p == 0 and (self.disc()//p)%p != 0:
        eigen = eigen + 1
    if p in self._eigen_tp:
      if d in self._eigen_tp[p]:
        self._eigen_tp[p][d][v] = eigen
      else:
        self._eigen_tp[p][d] = {v:eigen}
    else:
        self._eigen_tp[p] = {d:{v:eigen}}
    return eigen


  def eigenvalue_tp2_d(self, p, v, d):

    if p in self._eigen_tp2:
      if l in self._eigen_tp2[p]:
        if v in self._eigen_tp2[p][d]:
          return self._eigen_tp2[p][d][v]
    g = len(v)
    not_amb = self._not_ambiguous[d]
    change = lambda j: not_amb.index(j)
    for i in range(g):
      if v[i] != 0:
        break
    Q = self._iso_dict[not_amb[i]]
    w = vector(ZZ, g)
    for R, A in qf_find_p2_neighbors(Q, p, 1):
      Rtheta = R.theta_series(self._thetaN)
      Rpossibleisos = self._iso_dict_theta[Rtheta]
      if len(Rpossibleisos) == 1:
        Qiso = Rpossibleisos[0]
        j = self._iso_dict_inv[Qiso]
      else:
        for Qiso in Rpossibleisos:
          if Qiso.is_globally_equivalent_to(R):
            j = self._iso_dict_inv[Qiso]
            break
      if j in not_amb:
        X = R.is_globally_equivalent_to(Qiso, 1)
        X*= X.det()
        s = qf_spin_norm(self.Q0, self._transformations[Q]*A*X*self._transformations[Qiso]^-1)
        sk = nu(d, s)
        w[change(j)]+= sk
    v_dual = vector([v[change(j)]*ZZ(self._iso_dict[j].number_of_automorphisms()) for j in range(len(self._iso_dict)) if j in not_amb])
    eigen = v_dual*w/v_dual[i]
    if p in self._eigen_tp2:
      if d in self._eigen_tp2[p]:
        self._eigen_tp2[p][d][v] = eigen
      else:
        self._eigen_tp2[p][d] = {v:eigen}
    else:
        self._eigen_tp2[p] = {d:{v:eigen}}
    return eigen

  def ambiguous_forms(self):

    g = len(self._iso_dict)
    ds = [d for d in self.disc().divisors() if d.is_squarefree() or d != 1]
    ambs = {1:[]}
    not_ambs = {1:list(range(g))}
    for d in ds:
        ambs[d] = []
        not_ambs[d] = list(range(g))
    for i in range(g):
      R = self._iso_dict[i]
      cont = 0
      damb = []
      for A in R.automorphisms():
        if A.det() == 1:
          s = qf_spin_norm(R, A)
          for d in ds:
            if d not in damb and nu(d, s) == -1:
              ambs[d].append(i)
              not_ambs[d].remove(i)
              damb.append(d)
              cont+= 1
          if cont == len(ds):
            break
    self._ambiguous = ambs
    self._not_ambiguous = not_ambs

  def _rational_spaces_p_l1(self, p):

    hecke_ap = p^3+p^2+p+1
    disc = self.disc()
    Tp = self.Tp_l(p, 1)
    pol = Tp.charpoly()
    self._charpols[p] = pol
    fac = pol.factor()
    rational_factors = [fact[0] for fact in fac if fact[0].degree() == 1]
    rational_aps = [-fact[0] for fact in rational_factors]
    rational_aps.remove(hecke_ap)
    rational_spaces = []
    for ap in rational_aps:
      rk = (Tp - ap).left_kernel()
      if rk.rank() > 0:
        rational_spaces.append(rk)
      else:
        print "not rational space ap", self.disc(), p
    rational_spaces = [(Tp-ap).left_kernel() for ap in rational_aps]
    return rational_spaces

  def _rational_spaces_p_l(self, p, l):

    if l == 1:
        return self._rational_spaces_p_l1(p)
    disc = self.disc()
    Tp = self.Tp_l(p, l)
    pol = Tp.charpoly()
    self._charpols[p] = pol
    fac = pol.factor()
    rational_factors = [fact[0] for fact in fac if fact[0].degree() == 1]
    rational_aps = [-fact[0] for fact in rational_factors]
    rational_spaces = []
    for ap in rational_aps:
      rk = (Tp - ap).left_kernel()
      if rk.rank() > 0:
        rational_spaces.append(rk)
      else:
        print "not rational space ap", self.disc(), p
    rational_spaces = [(Tp-ap).left_kernel() for ap in rational_aps]
    return rational_spaces
    
  def _rational_vectors_l(self, l):

    disc = self.disc()
    p = 2
    while True:
      if disc%p != 0:
        rational_spaces_p = self._rational_spaces_p_l(p, l)
        if prod([x.rank() for x in rational_spaces_p]) == 1:
          return [rs.matrix() for rs in rational_spaces_p]
      p = p.next_prime()
      if p > 50:
        print "stable rank > 1?"
        break

  def rational_vectors(self):

    p = 2
    while self.disc()%p == 0:
      p = next_prime(p)
    self.Tp(p)
    self._ambiguous_forms()
    return [(l, self._rational_vectors_l(l)) for l in kron_ls(self.disc(), p)]

  def rational_vectors_without1(self):

    p = 2
    while self.disc()%p == 0:
      p = next_prime(p)
    self.Tp(p)
    self._ambiguous_forms()
    return [(l, self._rational_vectors_l(l)) for l in kron_ls(self.disc(), p) if l!=1]

  def decompose(self, d = 1, bound = 40):

    p = 2
    T = self.Tp_d(p, d)
    todo = [ ZZ**len(self._not_ambiguous[d]) ]
    decomp = []
    while todo:
        T = self.Tp_d(p, d)
        todo_next = []
        for V in todo:
            for A, is_irred in T.decomposition_of_subspace(V):
                if is_irred:
                    decomp.append(A)
                else:
                    todo_next.append(A)
        todo = todo_next
        p = p.next_prime()
        if p > bound:
            break
    return decomp + todo

  def eigentraces(self, space, bound, d = 1):
    return [ self.Tp_d(p, d).restrict(space).trace() for p in primes(bound) ]

  def eigentraces2(self, space, bound, d = 1):
    return [ self.Tp2_d(p, d).restrict(space).trace() for p in primes(bound) if self.disc()%p != 0]



#funciones para generar latex de cosas

def qf_latex(Q):

  R = PolynomialRing(ZZ, 'x, y, z, t, w')
  V = vector(R.gens())
  M = Q.matrix()
  return latex(V*M*V/2)

def table_latex(L, ncols, strings):
    """
    L = [[p, ap] for p in P]
    """
    s = "\\begin{tabular}{"
    for i in range(ncols):
        s+= "|r|r|"
    s+= "}\hline\n"
    a, b = strings
    for i in range(ncols):
        s+="$"+a+"$&$"+b+"$"
        if i < ncols-1:
            s+="&"
        else:
            s+="\\\\\hline\hline\n"
    n = len(L)
    nrows = min([nrows for nrows in range(0, n) if (0<n-(ncols-1)*nrows and n-(ncols-1)*nrows<=nrows)])
    if n%nrows == 0:
        lim = nrows
    else:
        lim = n%nrows
    for i in range(lim):
        for j in range(ncols):
            p, ap = L[j*nrows+i]
            s+= "$"+str(p)+"$&$"+str(ap)+"$"
            if j < ncols-1:
               s+="&"
            else:
               s+="\\\\\hline\n"
    for i in range(lim, nrows):
        for j in range(ncols-1):
            p, ap = L[j*nrows+i]
            s+= "$"+str(p)+"$&$"+str(ap)+"$"
            if j < ncols-2:
               s+="&"
            else:
               s+="&&\\\\\hline\n"
    s+= "\end{tabular}"
    return s

def pol_latex(L):

    d = len(L)
    s = ''
    for i in range(d):
        if i == 0:
            s+=str(L[i])
        elif i == 1:
            if L[i] == 1:
                s+='+X'
            elif L[i] == -1:
                s+='-X'
            elif L[i] > 0:
                s+='+'+str(L[i])+'X'
            else:
                s+=str(L[i])+'X'
        else:
            if L[i] == 1:
                s+='+X^'+str(i)
            elif L[i] == -1:
                s+='-X^'+str(i)
            elif L[i] > 0:
                s+= '+'+str(L[i])+'X^'+str(i)
            else:
                s+= str(L[i])+'X^'+str(i)
    return '$'+s+'$'

def euler_factor(N, p, l, cp, cp2):

    R = PolynomialRing(ZZ, 'X')
    X = R.0
    if N%p == 0:
        return (1+cp2*p*X)*(1-(cp+cp2*p+kronecker(p,l))*X+p^3*X^2)
    else:
        return 1-cp*X+(cp2+1+p^2)*p*X^2-p^3*cp*X^3+p^6*X^4

def euler_latex(N, p, l, cp, cp2):

    return pol_latex(euler_factor(N, p, l, cp, cp2).coefficients())
        

#funcion para verificar que la dimension paramodular de un primo
#es igual a la suma de las dimensiones de los espacios de formas
#modulares ortogonales

@parallel(10)
def verificar_dimension_primo(p, qmod):

     T = qmod.Tp_l(2, 1)
     qmod._ambiguous_forms()
     na = qmod._not_ambiguous
     return sum([len(na[l]) for l in na]) - 1 == dimension_paramodular_3_prime(p)

#cosas para verificar funciones L

def strLgp(C, sign, aps, ap2s):

    s = 'l_ap = {[\n'
    for i in range(len(aps)-1):
        p, ap = aps[i]
        s+='['+str(p)+','+str(ap)+'],\n'
    p, ap = aps[-1]
    s+='[' + str(p) + ',' + str(ap) + ']]};\n'
    s+= 'l_ap2 = {[\n'
    for i in range(len(ap2s)-1):
        p, ap = ap2s[i]
        s+='['+str(p)+','+str(ap)+'],\n'
    p, ap = ap2s[-1]
    s+='[' + str(p) + ',' + str(ap) + ']]};\n'
    s+= 'L_euler(p)={\n'
    s+= 'i=primepi(p);\n'
    s+= 'if(i>#l_ap, return(1+O(X)));\n'
    s+= 'if(l_ap[i][1]!=p,error("bad input"));\n'
    s+= 'ap=l_ap[i][2];\n'
    s+= 'if(i>#l_ap2, return(1-ap*X+O(X^2)));\n'
    s+= 'if(l_ap2[i][1]!=p,error("bad input"));\n'
    s+= 'ap2=l_ap2[i][2];\n'
    s+= 'if(ap2==+oo, return((1 - p*X) * (1 - (ap-p)*X + p^3*X^2)));\n'
    s+= 'if(ap2==-oo, return((1 + p*X) * (1 - (ap+p)*X + p^3*X^2)));\n'
    s+= 'return(1 - ap * X + p*(ap2+1+p^2) * X^2 - ap*p^3*X^3 + p^6*X^4);}\n'
    s+= 'L_dirichlet = direuler(p=2,prime(#l_ap+1)-1,1/L_euler(p));\n'
    s+= 'L = lfuncreate([L_dirichlet, 0, [-1,0,0,1], 4, ' + str(C)+', '+str(sign)+']);\n'
    s+= 'lfunorderzero(L)\n'
    return s

def checkL(C, sign, aps, ap2s, name):

    s = strLgp(C, sign, aps, ap2s)
    f = open('l'+name+'.gp', 'w')
    f.write(s)
    f.close()

def lqmod_rat_vecs(qmod):
    
    if qmod._eigen_tp != {}:
        print 'Existen vectores'
        ls = qmod._eigen_tp[qmod._eigen_tp.keys()[0]].keys()
        if 1 in ls:
            vecs1 = qmod._eigen_tp[qmod._eigen_tp.keys()[0]][1].keys()
            ls.remove(1)
            for i in range(len(vecs1)):
                v = vecs1[i]
                aps = [[p, qmod.eigenvalue_tp_l(p, v, 1)] for p in primes(24)]
                ap2s = [[p, qmod.eigenvalue_tp2_l(p, v, 1)] for p in primes(6)]
                C = qmod.disc()
                sign = 1
                name = str(C)+'_1_'+str(i+1)
                checkL(C, sign, aps, ap2s, name)
        if len(ls) == 1:
            l = ls[0]
            vecsl = qmod._eigen_tp[qmod._eigen_tp.keys()[0]][l].keys()
            for i in range(len(vecsl)):
                v = vecsl[i]
                aps = [[p, qmod.eigenvalue_tp_l(p, v, l)] for p in primes(24)]
                ap2s = [[p, qmod.eigenvalue_tp2_l(p, v, l)] for p in primes(6)]
                C = qmod.disc()
                sign = -1
                name = str(C)+'_'+str(l)+'_'+str(i+1)
                checkL(C, sign, aps, ap2s, name)

def buscar(D, g):

  qmod = quinary_module(quins[D][g][0])
  qmod.Tp(2)
  qmod._ambiguous_forms()
  lrv1 = []
  for l in kron_ls(D)[1:]:
      if len(qmod._not_ambiguous[l]) == 1:
          lrv1.append(l)
  return lrv1

def probar(D, g):

  qmod = quinary_module(quins[D][g][0])
  p = 2
  print D, g
  T = qmod.Tp(p)

