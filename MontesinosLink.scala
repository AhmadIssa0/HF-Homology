
package ahmad.hfhomology

import spire.math._
import spire.implicits._

/** Represents a Montesinos knot
 *
 *  See "A remark on the determinant of quasi-alternating links" - Qazaqzeh, Qublan
 *  Figure 2 for conventions. However, our tangles are reciprocals of those used in the paper.
 *  Thus, Figure 2(b) is the tangle -31/9 in our notation.
 *
 *  Our conventions for a Montesinos knot and a SFS over S^2 match up.
 *
 *  @param e0 same as e in the paper above, which is the same as the weight of the central vertex.
 *
 */

case class MontesinosLink(e0: SafeLong, tangles: Vector[Rational]) {
  /** Does this link satisfy condition of Theorem 3.4 of
   *  "Characterization of quasi-alternating Montesinos links" by Qazaqbeh, Chbili, Qublan.
   *  This is a sufficient condition to be QA.
   */
  def isQAByQCQ: Boolean = {
    // Must be sure that the Montesinos link is normalised
    if (isNormalised) {
      val n = tangles.length
      if (e0 == 0 || e0 >= n) true
      else if (e0 == 1) {
        tangles.indices.exists { i =>
          val ai = tangles(i).numerator
          val bi = tangles(i).denominator
          Rational(ai, ai - bi) > (tangles.slice(0, i) ++ tangles.slice(i+1, n)).min
        }
      } else if (e0 == n - 1) {
        tangles.indices.exists { i =>
          val s = tangles.map(x => 1/(1 - 1/x))
          tangles(i) > (s.slice(0, i) ++ s.slice(i+1, n)).min
        }
      } else false
    } else normalised.isQAByQCQ
  }

  /** Normalised means every tangle r = a/b satisfies 0 < b/a < 1.
   *
   */
  def isNormalised: Boolean =
    tangles.forall(_ > 1)

  def normalised: MontesinosLink = {
    val recips = tangles.map(r => 1/r)
    ???
  }
}
