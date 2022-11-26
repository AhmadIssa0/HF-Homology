
package ahmad.hfhomology

import spire.math._
import spire.implicits._

/** A class to represent HFK-hat.
  * 
  * @param rank A map from a pair (m, s) to rank(HFKHat_m(K, s)), where m is the Maslov grading
  * and s is the Alexander grading.
  *
  */
case class HFKHat(rank: Map[(Int, Int), Int]) {
	
}

object HFKHat {
  /**
    * There is a more general version for quasi-alternating links.
    * For a quasi-alternating link, HFK is determined by the Alexander 
    * polynomial and signature. More precisely, 
    *     HFK_m(K, s) = Z^|a_s|, m = s + signature/2.
    *
    * In fact, the full knot Floer complex is also determined by the
    * Alexander polynomial and signature. See "See "Cables of Thin Knots 
    * and Bordered Heegaard Floer Homology" by Ina Petkova.
    *
    * @return Returns HFK (hat) of the knot.
    * @param alexCoeffs Coefficients of symmetrized Alexander polynomial.
    * @param signature Signature of the knot.
    * @see See Theorem 10.3.3 of "Grid Homologies for knots and links" [OSS].
    */
  def quasialternatingKnot(alexCoeffs: Vector[Int], signature: Int): HFKHat = {
    require(signature % 2 == 0, s"Signature (signature=$signature) is not divisible by 2.")

    def loop(i: Int = 0): List[((Int, Int), Int)] = {
      // i is the current coefficient index
      if (i < alexCoeffs.length) {
        val degree = (alexCoeffs.length - 1)/2
        val alexGr = i - degree
        val maslovGr = alexGr + signature/2
        val rank = math.abs(alexCoeffs(i))
        if (rank == 0) 
          loop(i+1)
        else 
          (maslovGr, alexGr) -> rank :: loop(i + 1)
      } else {
        List()
      }
    }
    val rankMap = loop().toMap.withDefaultValue(0)
    HFKHat(rankMap)
  }
}
