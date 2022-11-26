
package ahmad.hfhomology

import spire.math._
import spire.implicits._

object LensSpace {

  /** Computes a correction term of p/q surgery on the unknot.
   *
   *  See Proposition 4.8 "Absolutely graded Floer homologies and intersection forms 
   *  for four-manifolds with boundary" - Ozsvath, Szabo.
   *
   *  Convention: In the paper L(p,q) = p/q surgery on unknot (see pg 183 of paper).
   *
   *  d(L(p,q), i) = -(pq - (2i + 1 - p - q)^2)/(4pq) - d(L(q,r), j),
   *  where p > q positive integers and relatively prime
   *        0 <= i <= p + q,
   *        r = p % q,
   *        j = i % q.
   *  @return d(-L(p, q), i)
   */
  def dInvariant(p: SafeLong, q: SafeLong, i: SafeLong): Rational = {
    if (p == 1) {
      0
    } else {
      require(p > 0 && q > 0, s"L(p,q), p and q must be positive. Given $p, $q")
      require(i >= 0 && i < p + q, "Parameter i must satisfy 0 <= i < p + q")
      val r = p % q
      val j = i % q
      val res = -Rational(p*q - (2*i + 1 - p - q)**2, 4*p*q) - dInvariant(q, r, j)
      res
    }
  }

  def dInvariants(p: SafeLong, q: SafeLong): Vector[Rational] = {
    require(p > 0, "p must be positive.")
    (0L until p.toLong).toVector.map(dInvariant(p, q, _))
  }

  

}
