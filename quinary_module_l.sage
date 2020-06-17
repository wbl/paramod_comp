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
  Dimension of the space of siegel modular forms of weight 3 and level p.
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

#######################################
#######################################
############# p1-neighbors ############
#######################################
#######################################


def qf_find_primitive_zeros_mod_p_general(Q, p):

  """
  Given a quinary regular quadratic form over ZZ, and an odd prime p,
  returns the primitive zeros mod p of Q.
  """
  w = vector((1, 0, 0, 0, 0))
  if Q(w)%p == 0:
    yield w
  for a in range(p):
    w = vector((a, 1, 0, 0, 0))
    if Q(w)%p == 0:
      yield w
    for b in range(p):
      w = vector((a, b, 1, 0, 0))
      if Q(w)%p == 0:
        yield w
      for c in range(p):
        w = vector((a, b, c, 1, 0))
        if Q(w)%p == 0:
          yield w
        for d in range(p):
          w = vector((a, b, c, d, 1))
          if Q(w)%p == 0:
            yield w


def qf_find_primitive_zeros_mod_p_regular(Q, p):

  """
  Given a quinary regular quadratic form over ZZ, and an odd prime p,
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
  Given a quinary quadratic form over ZZ, and a prime p,
  returns the nonsingular primitive zeros mod p of Q.
  """

  if Q.disc()%p != 0 and p != 2:
    for v in qf_find_primitive_zeros_mod_p_regular(Q, p):
      yield v
  elif Q.disc()%p != 0 and p == 2:
    for v in qf_find_primitive_zeros_mod_p_general(Q, p):
      yield v
  else:
    for v in qf_find_primitive_zeros_mod_p_general(Q, p):
      if Q.is_zero_nonsingular(v, p):
        yield v


def qf_find_p_neighbor_from_vec(Q, p, v, return_matrix = False):

  """
  Given a quinary quadratic form over ZZ, a prime p, and a vector
  v such that Q(v) = 0 (mod p^2), and v != 0 mod p, returns the
  p-neighbor associated to v.
  Copied from the qf package of sage, but with bugs fixed.
  """

  R = Q.base_ring()
  n = Q.dim()
  B2 = Q.matrix()

  ## Find a (dual) vector w with B(v,w) != 0 (mod p)
  v_dual = B2 * vector(v)     ## We want the dot product with this to not be divisible by 2*p.
  y_ind = 0
  while ((y_ind < n) and (v_dual[y_ind] % p) == 0):   ## Check the dot product for the std basis vectors!
      y_ind += 1
  if y_ind == n:
      raise RuntimeError("Oops!  One of the standard basis vectors should have worked.")
  w = vector([R(i == y_ind)  for i in range(n)])
  vw_prod = (v * Q.matrix()).dot_product(w)
  s = Q(v)
  if (s % p**2 != 0):
      al = (-s / (p * vw_prod)) % p
      v1 = v + p * al * w
      v1w_prod = (v1 * Q.matrix()).dot_product(w)
  else:
      v1 = v
      v1w_prod = vw_prod
  
  good_basis = extend_to_primitive([v1, w])
  for i in range(2,n):
      ith_prod = (good_basis[i] * Q.matrix()).dot_product(v)
      c = (ith_prod / v1w_prod) % p
      good_basis[i] = good_basis[i] - c * w  ## Ensures that this extension has <v_i, v> = 0 (mod p)
  ## Perform the p-neighbor switch
  good_basis[0]  = vector([x/p  for x in good_basis[0]])    ## Divide v1 by p
  good_basis[1]  = good_basis[1] * p                          ## Multiply w by p
  ## Return the associated quadratic form
  M = matrix(good_basis)
  new_Q = deepcopy(Q)                        ## Note: This avoids a circular import of QuadraticForm!
  if hasattr(new_Q, '__theta_vec'):
      delattr(new_Q, '__theta_vec')
  if hasattr(new_Q, '__automorphisms_pari'):
      delattr(new_Q, '__automorphisms_pari')
  if hasattr(new_Q, '__number_of_automorphisms'):
      delattr(new_Q, '__number_of_automorphisms')
  new_Q.__init__(R, M * Q.matrix() * M.transpose())
  if return_matrix:
      return new_Q, M.transpose()
  else:
      return new_Q
  return QuadraticForm(R, M * Q.matrix() * M.transpose())

def qf_find_p_neighbors(Q, p, return_matrix = False):

  """
  Given a quinary quadratic form over ZZ, and a prime p,
  returns the p-neighbors of Q.
  """

  for v in qf_find_primitive_zeros_mod_p_nonsingular(Q, p):
    if return_matrix:
      Q1, M1 = qf_find_p_neighbor_from_vec(Q, p, v, return_matrix = return_matrix)
      Q2, M2 = qf_reduction_pari(Q1, return_matrix = 1)
      yield Q2, M1*M2
    else:
      Q1 = qf_find_p_neighbor_from_vec(Q, p, v, return_matrix = return_matrix)
      yield qf_reduction_pari(Q1)

def qf_find_genus(Q, p):

  """
  Finds the genus of a quinary qf using p-neighbors.
  WARNING: I don't think this works in general, maybe for
  squarefree discriminant.
  """

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

#######################################
#######################################
############# p2-neighbors ############
#######################################
#######################################

def primitivize(v, p):

  """
  Returns the multiple of v mod p that has a 1 in the
  last possible coordinate.
  """
  i = (v%p).nonzero_positions()[-1]
  v = (v*inverse_mod(v[i], p))%p
  return v

def primitivize2(v, p):

  """
  Returns the multiple of v mod p^2 that has a 1 in the
  last possible coordinate.
  """

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
  Given a quinary quadratic form over ZZ, a prime p, Q.disc()%p != 0, and an isotropic
  plane mod p, returns another plane Z, such that  <X[i], Z[j]> = delta_ij.
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
  Given a quinary quadratic form over ZZ, a prime p, Q.disc()%p != 0, X, Z
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
  Given a quinary quadratic form Q, a prime p, Q.disc()%p != 0, X, Z isotropic planes
  mod p^2 such that Z is hyperbolic complement of X mod p^2. Returns the
  isotropic planes X1 mod p^2 such that X=X1 mod p, and X1 and Z are hyperbolic
  complement mod p^2.
  """

  x1, x2 = X
  z1, z2 = Z
  for a in range(p):
      x1p = x1 + p*a*z2
      x2p = x2 - p*a*z1
      yield([x1p, x2p])

def qf_find_p2_neighbor_from_plane(Q, p, X, Z, return_matrix = False):

  """
  Given a quinary quadratic form Q, a prime p, Q.disc()%p != 0, X, Z isotropic planes
  mod p^2 such that Z is hyperbolic complement of X mod p^2, returns the p2-neighbor
  associated.
  """

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
  Given a quinary quadratic form and a prime p returns an isotropic plane
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
  Given a quinary quadratic form and a prime p, returns a basis v_i of ZZ^5,
  such that: <v_i, v_j> = 1 iff i + j = 5, and 0 otherwise.
  """

  v1, v2 = qf_isotropic_plane_random(Q, p)
  v4, v3 = qf_hyperbolic_complement(Q, p, [v1, v2])
  v5 = qf_orthogonal_random(Q, p, [v1, v2, v3, v4])
  return [v1, v2, v3, v4, v5]

def qf_isotropic_planes(Q, p):

  """
  Given a quinary quadratic form and a prime p, Q.disc()%p != 0, returns the isotropic planes
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

  """
  Given a quinary quadratic form over ZZ, and a prime p,
  returns the p2-neighbors of Q.
  """

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

#######################################
#######################################
############## reduction ##############
#######################################
#######################################


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

#######################################
#######################################
############## spin norm ##############
#######################################
#######################################


def qf_symmetry(Q, v):

  """
  Given a quinary quadratic form and a vector v, returns the matrix
  of the symmetry of v.
  """

  return identity_matrix(5) - v.column()*matrix(v)*Q.matrix()/Q.base_change_to(QQ)(v)

def qf_automorphism_symmetries_proper(Q, A):

  """
  Given a quinary quadratic form and a proper autometry A, returns the
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
  Given a quinary quadratic form Q, and an autometry A, returns the
  spin norm of A.
  """

  return prod([Q.base_change_to(QQ)(v) for v in qf_automorphism_symmetries_proper(Q, A)]).squarefree_part()


#######################################
#######################################
########## Quinary module #############
#######################################
#######################################


def nu(d, n):

  """
  Given natural numbers d, and n returns the the character nu_d(n).
  The character is defined in primes p as nu_d(p) = -1 iff p|d.
  """
  
  return (-1)^len(gcd(d, n).prime_divisors())

class quinary_module():
  
  """
  Class of quinary qfs module used to compute
  quinary orthogonal modular forms.
  """

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

    """
    Returns the theta kernel of the module.
    """

    Tp = self.Tp_d(p, 1)
    h = len(self._iso_dict)
    vt = [self._iso_dict[i].theta_series(h) for i in range(h)]
    M = matrix(h, [vt[i][j] for i in range(h) for j in range(h)])
    return M.kernel()

  def theta_kernel_dimension(self):

    """
    Returns the dimension of theta kernel of the module.
    """

    return self.theta_kernel().dimension()

  def _Tp_init(self, p):

    """
    Initialize the module, finds the genus using p-neighbors
    and Tp.
    """

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

    """
    Returns the data to compute the Hecke operator. 
    Not very useful for the user.
    """

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

      """
      Returns the Hecke operator Tp1 at p with character nu_d, with nu_1 the
      trivial character.
      """

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

    """
    Returns the data to compute the Hecke operator.
    Not very useful for the user.
    It doesn't work for p|D, where D is the discriminant of the genus.
    """

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

      """
      Returns the Hecke operator Tp2 at p with character nu_d, with nu_1 the
      trivial character.
      It doesn't work for p|D, where D is the discriminant of the genus.
      """

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

    """
    Given a vector v that is a Hecke-eigenvector for
    the character nu_d, it returns the eigenvalue
    of Tp1 for p.
    """

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

    """
    Given a vector v that is a Hecke-eigenvector for
    the character nu_1, it returns the eigenvalue
    of Tp1 for p.
    """

    d = 1
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
    eigen = v_dual*w/v_dual[i]
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

    """
    Given a vector v that is a Hecke-eigenvector for
    the character nu_d, it returns the eigenvalue
    of Tp2 for p.
    """

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

    """
    Function that computes the qfs in the genus that have an autometry
    with nu_d = -1, for all d|D.
    """

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

  def decompose(self, d = 1, bound = 40):

    """
    Finds the decomposition in Hecke-eigenspaces.
    """
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

    """
    Returns the traces for Tp1 of the Hecke-eigenspaces.
    """

    return [ self.Tp_d(p, d).restrict(space).trace() for p in primes(bound) ]

  def eigentraces2(self, space, bound, d = 1):

    """
    Returns the traces for Tp2 of the Hecke-eigenspaces.
    """

    return [ self.Tp2_d(p, d).restrict(space).trace() for p in primes(bound) if self.disc()%p != 0]
