
package ahmad.hfhomology

import spire.math._
import spire.implicits._

object MontesinosIntersectionForm {

  // Vertex together with an embedding
  // (1, 2) in coeffs means 1*e2
  type Coeffs = Vector[(Int, Int)]
  case class Node(w: Int, coeffs: Coeffs) {
    def maxBasisVector: Int = (0 +: coeffs.map(_._2)).max
  }

  case class Embedding(e0: Node, legs: Vector[Vector[Node]]) {
    def setCentralCoeffs(coeffs: Coeffs): Embedding =
      //this.copy(e0 = e0.copy(coeffs = coeffs))
      Embedding(Node(e0.w, coeffs), legs)

    def setLegCoeffs(leg: Int, i: Int, coeffs: Coeffs): Embedding = {
      Embedding(
        e0,
        legs.updated(
          leg,
          legs(leg).updated(i, Node(legs(leg)(i).w, coeffs))
        )
      )
    }

    // This is the transpose of the inclusion map
    def toMatrix: Matrix = {
      // number of nodes, number of columns in matrix
      val cols = 1 + legs.map(_.length).sum

      // number of rows is given by max n such that e_n is used
      val rows = (e0.maxBasisVector +:
        legs.map(x => (0 +: x.map(_.maxBasisVector)).max)).max

      val images = e0.coeffs +: legs.flatMap(_.map(_.coeffs))

      def getCoeff(c: Coeffs, i: Int): Int = {
        c.find(_._2 == i) match {
          case Some((a, _)) => a
          case None => 0
        }
      }

      Matrix (
      for (i <- 0 until cols toVector) yield
        for (j <- 0 until rows toVector) yield
          SafeLong(getCoeff(images(i), j + 1))
      )
    }
  }

  implicit class RichCoeffs(c: Coeffs) {
    /**
     * returns dot product, assuming coeffs are basis for
     *         std negative definite lattice.
     */
    def dot(c2: Coeffs): Int = {
      c.map {
        case (a, n) => {
          c2.find(_._2 == n) match {
            case Some((b, _)) => -1 * a * b
            case None => 0
          }
        }
      }.sum
    }

    /** Absolute value of self pairing. */
    def norm: Int = -1 * dot(c)
  }

  /**
   * Enumerates all lattice elements with norm at most norm.
   * Lattice elements are linear combinations of elements of basis.
   */
  def enumCoeffs(basis: Vector[Int], norm: Int): Vector[Coeffs] = {
    basis match {
      case b +: rest => {
        if (norm > 0) {
          val m: Int = sqrt(norm.toDouble).round.toInt
          val coeffs: Vector[Coeffs] =
            for (
              i <- (1 to m).toVector;
              cs <- enumCoeffs(rest, norm - i * i);
              sgn <- -1 to 1 by 2
            ) yield {
              (sgn * i, b) +: cs
            }
          coeffs ++ enumCoeffs(rest, norm).map((0, b) +: _)
        } else {
          enumCoeffs(rest, norm).map((0, b) +: _)
        }
      }
      case _ => if (norm < 0) Vector() else Vector[Coeffs](Vector())
    }
  }


  /**
   * When we know some of the coefficients of an embedding
   * of a node and we want work out more coefficients using
   * the condition that Q(node, some other node) = k and
   * Q(node, node) <= norm
   * @param coeffs Coefficients which we only partially know.
   * @param nbrCoeffs Want Q(coeffs, nbrCoeffs) = k.
   */
  def extendCoeffs(
    coeffs: Coeffs,
    nbrCoeffs: Coeffs,
    k: Int,
    norm: Int
  ): Vector[Coeffs] = {
    if (norm < 0) Vector()
    else if (norm == 0 || nbrCoeffs.isEmpty) {
      if (coeffs.dot(nbrCoeffs) == k)
        Vector(coeffs)
      else
        Vector()
    } else {
      // e_n is basis element we're working with
      val (a, e_n) = nbrCoeffs(0) // nbrCoeffs is not empty
      coeffs.find(_._2 == e_n) match {
        case Some((b, _)) => // already assigned a coefficient of e_n
          extendCoeffs(
            coeffs,
            nbrCoeffs.tail,
            k + a * b,
            norm
          )
        case None => { // loop over all possible coefficients of e_n
          val m: Int = sqrt(norm.toDouble).round.toInt
            (-m to m).toVector.flatMap(i =>
                extendCoeffs(
                  (i, e_n) +: coeffs,
                  nbrCoeffs.tail,
                  k + a*i,
                  norm - i*i
                )
            )
        }
      }

    }
  }

  /**
    * Sequences of non-increasing positive integers with norm given
    * by norm.
    */
  def vectorsOfNorm(norm: Int): Vector[Vector[Int]] = {
      def loop(
        rem: Int = norm,
        maxInRest: Int = norm
      ): Vector[Vector[Int]] = {
        if (rem == 0) Vector(Vector())
        else {
          val n = min(maxInRest, sqrt(rem.toDouble).toInt)
          for (
            i <- (1 to n).toVector;
            lst <- loop(rem - i * i, i)
          ) yield (i +: lst)
        }
      }
    loop()
  }


  /**
   * All embeddings of negative definite plumbing
   * of SFS into the standard negative definite lattice.
   */
  def embeddings(
    embedding: Embedding,
    currLeg: Int = -1,
    indexInLeg: Int = 0,
    newLabel: Int = 1
  ): Vector[Embedding] = {
    if (currLeg == -1) { // embed central vertex first
      vectorsOfNorm(-embedding.e0.w)
        .flatMap(seq => {
        val coeffs = seq.zip(1 to seq.length)
        val e = embedding.setCentralCoeffs(coeffs)
        embeddings(e, currLeg = 0, indexInLeg = 0, newLabel = seq.length + 1)
      })
    } else if (currLeg >= embedding.legs.length) { // finished all the legs
      Vector(embedding)
    } else { // in a leg
      // assign all possible allowed coefficients to current node then recurse
      val node = embedding.legs(currLeg)(indexInLeg)
      val above: Node =
        if (indexInLeg == 0) embedding.e0
        else embedding.legs(currLeg)(indexInLeg - 1)
      val norm = -node.w
      // possibilities for coefficients which pair correctly with node above
      // may have norm less than required
      //val possCoeffs = enumCoeffs(basis, norm).filter(_.dot(above.coeffs) == 1)
      val possCoeffs = extendCoeffs(Vector(), above.coeffs, 1, norm)

      // Want all nodes which have coefficients assigned
      // which are not adjacent to current node.
      val nonAdjNodes: Vector[Node] = {
        val inOtherLegs = (0 until currLeg).toVector
          .flatMap(embedding.legs(_))
        val inCurrLeg = embedding.legs(currLeg).take(indexInLeg - 1)
        val central = if (indexInLeg == 0)
            Vector[Node]()
        else Vector(embedding.e0)
        inOtherLegs ++ inCurrLeg ++ central
      }

      // Coefficients for already used basis elements
      val impliedCoeffs: Vector[Coeffs] =
        nonAdjNodes.foldLeft(possCoeffs) { (pCoeffs, n) => {
          pCoeffs.flatMap( coeffs =>
            extendCoeffs(coeffs, n.coeffs, 0, norm)
          )
        }}

      // Extend implied coeffs to coefficients of new basis elements
      // so that the image has the correct self-pairing
      impliedCoeffs.flatMap(coeffs => {
        // Vector[Int] sequences to fill in remainder
        val completedEmbeddings: Vector[Vector[Embedding]] =
        for (v <- vectorsOfNorm(norm + coeffs.dot(coeffs)))
        yield {
          // fullCoeffs is a possible completed image of the node
          val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
            .filter(_._1 != 0) // don't want to include 0 coefficients
          // set this node to have fullCoeffs as coefficients and recurse
          val filledEmbedding = embedding.setLegCoeffs(currLeg, indexInLeg, fullCoeffs)
          // are we at the last node of this leg?
          if (filledEmbedding.legs(currLeg).length == indexInLeg + 1)
            embeddings(filledEmbedding,
              currLeg = currLeg + 1,
              indexInLeg = 0,
              newLabel = newLabel + v.length
            )
          else
            embeddings(filledEmbedding,
              currLeg = currLeg,
              indexInLeg = indexInLeg + 1,
              newLabel = newLabel + v.length
            )
        }
        completedEmbeddings.flatten
      })
    }

  }

  /**
    * Embeddings of the standard negative definite plumbing for SFS over S^2
    * (with conventions as in SFSOverS2.scala), into -Z^n the std neg. def.
    * lattice.
    */
  def SFSEmbeddings(sfs: SFSOverS2): Vector[Embedding] = {
    // TODO: Make sure the SFS is oriented correctly.
    val std: SFSOverS2 = sfs.stdForm
    val legs: Vector[Vector[Node]] =
      std.coeffs.map(c =>
        linearChain(c.numerator.toInt, c.denominator.toInt)
          .map(Node(_, Vector())))
    val embedding = Embedding(Node(std.e0.toInt, Vector()), legs)
    embeddings(embedding)
  }


  /**
    * Expresses a fraction p/q = numer/denom < -1 as
    * p/q = a0 - 1/(a1 - 1/(a2 - ... 1/a_n))
    * @returns Vector(a0, a1, ..., a_n)
    */
  def linearChain(p: Int, q: Int): Vector[Int] = {
    require(p/q <= -1, s"Require input $p/$q = ${p/q} <= -1")
    if (q < 0) linearChain(-p, -q)
    else if (q == 1) Vector(p)
    else {
      val a = p/q - 1
      // -5/3 == -1, so we subtract 1 to get -5/3 == -2 + ...
      // p/q = a - 1/r
       // r = q/(aq - p)     
      a +: linearChain(q, a*q - p)
    }
  }

  def linearChain(r: Rational): Vector[Int] = {
    val p = r.numerator.toInt
    val q = r.denominator.toInt
    linearChain(p, q)
  }

}
