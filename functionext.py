import math
import random
import secrets

from sympy.ntheory import isprime
from tinyec import ec


class NoGeneratorPointException(Exception):
  pass

def find_generator_point(a, b, p):
  for x in range(p):
      rhs = (x**3 + a * x + b) % p
      if legendre_symbol(rhs, p) == 1:  # RHS is a quadratic residue
          y = tonelli_shanks(rhs, p)
          return (x, y)
  raise NoGeneratorPointException

def legendre_symbol(a, p):
  ls = pow(a, (p - 1) // 2, p)
  return -1 if ls == p - 1 else ls

def tonelli_shanks(n, p):
  assert legendre_symbol(n, p) == 1, "n is not a quadratic residue modulo p"
  q = p - 1
  s = 0
  while q % 2 == 0:
      q //= 2
      s += 1

  if s == 1:
      return pow(n, (p + 1) // 4, p)

  for z in range(2, p):
      if legendre_symbol(z, p) == -1:
          break

  m = s
  c = pow(z, q, p)
  t = pow(n, q, p)
  r = pow(n, (q + 1) // 2, p)

  while t != 1:
      i = 0
      t_i = t
      while t_i != 1:
          t_i = pow(t_i, 2, p)
          i += 1

      b = pow(c, pow(2, m - i - 1), p)
      r = r * b % p
      t = t * b * b % p
      c = b * b % p
      m = i
  return r

def is_singular(a, b, p):
  discriminant = (4*a**3 + 27*b**2) % p
  return discriminant == 0

def is_anomalous(p, n):
  return p == n

def is_supersingular(p, n):
  if p in [2, 3] or not isprime(p):
      return False
  return (p+1 - n) % p == 0

def validate_curve(a, b, p, G, n, h):
  if h < 1:
      return False
  if p == 0:
      return False
  elif isinstance(G, tuple) and len(G) == 2:
      x, y = G
      if (y*y - x*x*x - a*x - b) % p != 0:
          return False
      try:
          field = ec.SubGroup(p, G, n, h)
      except NoGeneratorPointException:
          return False
      ec.Curve(a, b, field, "random_curve")
  else:
      return False
  order = n
  if h != field.h:
      return False
  if is_singular(a, b, p):
      return False
  if is_anomalous(p, order):
      return False
  if is_supersingular(p, order):
      return False
  return True

def get_prime_for_p():
  while True:
      number = random.getrandbits(256)
      if number % 2 != 0 and isprime(number):
          return number
class ECCParameters:
  def __init__(self, p, a, b, G, n, h):
      self.p, self.a, self.b, self.G, self.n, self.h = p, a, b, G, n, h

class ECPoint:
  def __init__(self, x, y):
      self.x, self.y = x, y
    
def randbelow(n):
  return secrets.randbelow(n)

def generate_private_key(params):
  return randbelow(params.n - 1)
  
def ec_addition(P, Q, params):
  # Verifica si P o Q son el punto en el infinito
  if P is None:
      return Q
  if Q is None:
      return P

  # Verifica si P o Q son el punto en el infinito
  if P.x is None and P.y is None:
      return Q
  if Q.x is None and Q.y is None:
      return P

  # Verifica si P es el negativo de Q
  if P.x == Q.x and (P.y + Q.y) % params.p == 0:
      return ECPoint(None, None)

  # Calcula la pendiente de la línea entre P y Q
  if P.x == Q.x and P.y == Q.y:
      m = (3 * P.x * P.x + params.a) * pow(2 * P.y, -1, params.p) % params.p
  else:
      m = (Q.y - P.y) * pow(Q.x - P.x, -1, params.p) % params.p

  # Calcula las coordenadas del punto resultante
  x = (m * m - P.x - Q.x) % params.p
  y = (m * (P.x - x) - P.y) % params.p

  return ECPoint(x, y)

def ec_scalar_multiplication(P, scalar, params):
  result = ECPoint(None, None)
  current = P
  while scalar:
      if scalar & 1:
          result = current if result.x is None else ec_addition(result, current, params)
      current = ec_addition(current, current, params)
      scalar >>= 1
  return result

def evaluate(candidate):
    a, b, p, G, n, h = candidate
    if not validate_curve(a, b, p, G, n, h):
        return 0,

    expected_order = p + 1
    lower_bound = expected_order - 2 * math.isqrt(p)
    upper_bound = expected_order + 2 * math.isqrt(p)

    hasse_score = max(0, (upper_bound - abs(n - expected_order)) / (upper_bound - lower_bound))

    attack_resistance_score = 1 if n > expected_order else 0

    fitness = 0.4 * math.log(n) + 0.2 * hasse_score * math.log(n) + 0.4 * attack_resistance_score

    return fitness,