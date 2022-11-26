
package ahmad.hfhomology

import spire.math._
import spire.implicits._


case class Forest[A](trees: Vector[Tree[A]]) {
  override def toString: String =
    trees.mkString("\n")
  def fold[B](f: A => B): Forest[B] =
    Forest(trees.map(t => t.fold(f)))
}

object Forest {
  type Weight = Int
  import IntersectionForm.Coeffs

  implicit class ForestOps(forest: Forest[(Weight, Coeffs)]) {
    /**
      *  cob(i) = (c, j) means want to relabel e_i by c*e_j
      */
    def changeBasis(cob: Map[Int, (Int, Int)]): Forest[(Weight, Coeffs)] = {
      forest.fold { case (w, coeffs) =>
        val newCoeffs = coeffs.map({ c =>
          val (s, j) = cob(c._2)
          (c._1*s, j)
        }).sortBy(_._2)
        (w, newCoeffs)
      }
    }

    /**
      *  Checks whether the forest, assumed to consist of a tree and an 
      *  integer changemaker contains a marked crossing.
      * 
      *  Tries to find a basis vector e_i with coefficient 1 in the changemaker vector,
      *  such that there are exactly two vertices v_1 and v_2 of the tree with
      *  v_1 =  e_i + (things not related to e_i)
      *  v_2 = -e_i + (things not related to e_i).
      *  In this case, adding an edge (crossing in link) between v_1 and v_2
      *  we get a new embedding:
      *  v'_1 = e_0 + e_i + (things not related to e_i or e_0)
      *  v'_2 = -e_0 - e_i + (things not related to e_i or e_0)
      *  where e_0 is a new basis vector.
      *  Moreover, the new edge (crossing in link) is a marked crossing,
      *  so it is an unknotting crossing.
      * 
      *  The existence of such a marked crossing shows that the 3-manifold
      *  representing tree is integer surgery on a knot in S^3.
      */
    def markedCrossing: Option[Int] = {
      require(forest.trees.length == 2 && forest.trees(1).vertices.length == 1)
      val verts: Vector[Coeffs] = forest.trees(0).vertices.map(_._2)
      val cm: Coeffs = forest.trees(1).vertices(0)._2

      def getCoeff(coeffs: Coeffs, n: Int) = coeffs.find(_._2 == n) match {
        case Some((c, n)) => c
        case None => 0
      }

      // basis vectors in changemaker vector with coefficient 1
      val basis1 = cm.takeWhile(_._1 == 1).map(_._2)
      // for each element in basis1, get all coefficients of it in verts
      val basisCoeffs = basis1.map { n =>
        verts.map(coeffs => getCoeff(coeffs, n))
      }
      basisCoeffs.map(_.filter(_ != 0))
        .zipWithIndex
        .find({case (coeffs, e_i) => // non-zero coeffs of some e_i in tree
        coeffs.length == 2 && coeffs(0) == -coeffs(1) && (coeffs(0) == 1 || coeffs(0) == -1)
        })
        .map(_._2)
    }

  }
}
