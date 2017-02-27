=begin
Using the phrase - Math.sqrt(n).to_i - to find the integer squareroot of an
integer was found to produce incorrect results for n > ~2**52 = 4,503,599,627,370,496.

This bug was raised on the Ruby issues tracker threads listed below:

https://bugs.ruby-lang.org/issues/13219
https://bugs.ruby-lang.org/issues/13250

where techniques and code to correct the bug were presented and discussed.

This code is a fork of bechmarks of methods collected by Nathan Zook, 
https://github.com/NathanZook/ruby_sqrt, which I have modified and added to.

At the time of writing, Ruby has added the method Integer#isqrt to class Integer,
to provide as a fast C implementation of Newton's method to compute the integer
squareroot of arbitrary sized integers, as shown at the lines in the files below.

bignum.c, starting at line 6772
https://bugs.ruby-lang.org/projects/ruby-trunk/repository/revisions/57705/entry/bignum.c

numeric.c, starting at line 5131
https://bugs.ruby-lang.org/projects/ruby-trunk/repository/revisions/57705/entry/numeric.cRuy
=end


# Core Algorithm by Paul Zimmerman, article entitled
# Karatsuba Square Root
# https://hal.inria.fr/inria-00072854/document
# Presumably used in GMP.

# Personal computations derived from implementation details (page 5)
# n >= b**4 / 4
# b = 2**64**k
# n * 4 >= b ** 4
# n.length + 2 >= b.length * 4
# (n.length + 2) >> 2 >= b.length
# (n.length + 2) >> 2 >= 64 * k
# ((n.length + 2) >> 2) / 64 = k

def sqrtrem(n)
  nlength = n.bit_length
  if nlength >= (64 * 4 - 2)
    bbits = (n.bit_length + 2 >> 2) / 64 * 64
  elsif nlength >= (32 * 4 - 2)
    bbits = (n.bit_length + 2 >> 2) / 32 * 32
  elsif nlength >= (16 * 4 - 2)
    bbits = (n.bit_length + 2 >> 2) / 16 * 16
  elsif nlength >= 54 # Math.sqrt uses floating point double arithmetic, which gets us what we need
    bbits = (n.bit_length + 2 >> 2) / 8 * 8
  else
    s = Math.sqrt(n).to_i
    r = n - s * s
    return [s, r]
  end

  b = 1 << bbits
  bmask = b - 1
  a3 =  n >> bbits * 3
  a2 = (n >> bbits * 2) & bmask
  a1 = (n >> bbits    ) & bmask
  a0 =  n               & bmask

  i, j = sqrtrem((a3 << bbits) + a2)
  q, u = ((j << bbits) + a1).divmod(i << 1)
  s = (i << bbits) + q
  r = (u << bbits) + a0 - q ** 2

  if r < 0
    r += (s << 1) - 1
    s -= 1
  end

  [s, r]
end

def sqrt_z(n)
  raise if n < 0
  return n if n < 2
  s, r = sqrtrem(n)
  s
end


class Integer
  def irootn(n)
    return nil if self < 0 && n.even?
    raise "root n is < 2 or not an Integer" unless n.is_a?(Integer) && n > 1
    num  = self.abs
    bits_shift = (num.bit_length)/n + 2
    root, bitn_mask = 0, (1 << bits_shift)
    until (bitn_mask >>= 1) == 0
      root |= bitn_mask
      root ^= bitn_mask if root**n > num
    end
    root *= (self < 0 ? -1 : 1)
  end

  def iroot2; irootn(2) end    
end

def isqrt1(n)
  r = 0
  x = 1 << ((n.bit_length >> 1 ) << 1)
  until x == 0
    t = r | x
    r >>= 1
    (n -= t; r |= x) if n >= t
    x >>= 2
  end
  r
end

def newton_loop(n, x)
  y = (x + n/x) / 2
  while y != x
    x = y
    y = (x + n/x) / 2
  end

  x
end

def newton_faster(n)
  raise if n < 0
  return n if n < 2

  bits = (n.bit_length - 1 & -2) - 52
  top = bits > 0 ? n >> bits : n
  r0 = Math.sqrt(top).to_i
  x = bits > 0 ? r0 << (bits >> 1) : r0

  newton_loop(n, x)
end

def newtons_fast(n)
  raise if n < 0
  return n if n < 2
  x = 1<<((n.bit_length+1)/2)

  newton_loop(n, x)
end

# Newton's method coded in C for Ruby Integer#sqrt method
def newton_rbsqrt(n)
  return nil if n < 0
  return n if n < 2
  b = n.bit_length
  x = 1 << (b-1)/2 | n >> (b/2 + 1)
  while (t = n / x) < x; x = ((x + t) >> 1) end
  x
end

# Inspired by the second answer here:
# http://cs.stackexchange.com/questions/37596/arbitrary-precision-integer-square-root-algorithm
# Released under the Ruby license.

def ins_find_initial_exponent(nbits)
  nbits = nbits / 2 + 2 while nbits > 53
  nbits
end

def ins_find_initial_r(n, e0)
  bits = (n.bit_length - 1 & -2) - 52
  top = bits >= 0 ? n >> bits : n << bits

  float = Math.sqrt(top)
  raise "Out of bounds first round" if float > (1 << 27) or float < (1 << 26)

  r = ((1 << e0 + 26) / float).to_i
  raise "Out of bounds first r" if r > 1 << e0 or r < 1 << e0 - 1
  r
end

def ins_core(n, e_bits, r, exp)
  x = n >> exp - e_bits
  while e_bits < exp >> 1 do
    old_bits = e_bits
    e_bits <<= 1
    w = r ** 2
    x = n >> exp - e_bits
    e = 1 << e_bits
    wx = w * x >> e_bits
    if e > wx
      d = e - wx
      sign = 1
    else
      d = wx - e
      sign = -1
    end

    r_delta = sign * (r * d >> old_bits + 1)
    r = r * (1 << old_bits) + r_delta

  end
  [e_bits, r, x]
end


def inverse_newton_sqrt(n)
  raise if n < 0
  return Math.sqrt(n).to_i if n < 1 << 53

  n_bits = n.bit_length
  exp = (n.bit_length - 1) & -2
  e_0 = ins_find_initial_exponent(n_bits)
  r = ins_find_initial_r(n, e_0)
  e_bits, r, x = ins_core(n, e_0, r, exp)
  root = r * x >> (e_bits << 1) - (exp >> 1)
  root += 1 if n > root * root + (root << 1)
end

def valid_inverse_newton_sqrt(n)
  result = inverse_newton_sqrt(n)
  s = result * result
  limit = result * 2
  raise "Root too big (#{result})" unless s <= n
  raise "Root too small (#{result})" unless n - s <= limit
  result
end

require 'benchmark/ips'

[50, 500, 1000, 2000, 4000, 5000].each do |exp|
  Benchmark.ips do |x|
    n = 10**exp
    puts "integer squareroot tests for n = 10**#{exp}"
    x.report("newtons_fast(n)") { newtons_fast(n) }
    x.report("newton_faster(n)") { newton_faster(n) }
    x.report("newton_rbsqrt(n)") { newton_rbsqrt(n) }
    x.report("sqrt_z(n)") { sqrt_z(n) }
    x.report("inverse newton(n)") { inverse_newton_sqrt(n) }
    x.compare!
  end
end



