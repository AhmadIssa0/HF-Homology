 
package ahmad.hfhomology

import spire.implicits._
import spire.math._

object Spin {

  /**  Let X^4 be a plumbed 4-manifold with boundary M, a Seifert fibered space over S^2.
    *  Suppose that -M bounds a rational homology ball U.
    *  Let A be a matrix representing the inclusion H_2(X) -> H_2(X \cup U).
    *  Let v be a vector representing a characteristic sublink of X.
    *  Then the spin structure of M represented by v extends over U if and only if
    *  Av = (1,1,...,1)^t.
    *  We enumerate all such v.
    */
  def spinStructures(A: Matrix) = {
    // Embedding of vertices are columns.
    // Want to solve Av = (1,1,...,1)^t for all v (with Z_2 coefficients).
    val mats = A.extendedSmithForm
    val D = mats._1
    val L = mats._2
    val R = mats._3
    //assert(D == L*A*R)
    // D = L A R.
    // So D (R^-1 v) = LAR (R^-1 v) = L(1,1,...,1)^t.
    // We solve for x = R^-1 v, then recover v.
    val n = A.nCols
    val char = Matrix.fromFunction(nRows = n, nCols = 1, (_,_) => 1)
    val Lchar = L*char
    // Solving Dx = Achar for x (with Z_2 coeffs).
    val Ddiag = D.diagonalElements
    val possCoeffs =
      for (i <- (0 until n).toVector) yield {
        if (Ddiag(i) % 2 == 0) {
          if (abs(Lchar.mat(i)(0)) % 2 == 0) {
            Vector(0,1)
          } else Vector()
        } else {
          if (abs(Lchar.mat(i)(0)) % 2 == 1)
            Vector(1)
          else
            Vector(0)
        }
      }


    def sequence[A](as: Vector[Vector[A]]): Vector[Vector[A]] = as match {
      case Vector() => Vector(Vector())
      case b +: cs =>
        for (x <- b;
          ys <- sequence(cs))
        yield (x +: ys)
    }

    val xs = sequence(possCoeffs)
    val vs = xs.map(s => (R*Matrix(Vector(s)).transpose).map(abs(_) % 2))
    vs
  }

  /**  As in `spinStructures`, A : H_2(X) -> H_2(X \cup U) (vertices map to columns)
    *  We assume that X is a positive definite plumbing.
    *  If v is a characteristic sublink then extending over v then
    *  mu(M, v) = signature(X) - v.v
    */
  def muBar(A: Matrix, v: Matrix): SafeLong = {
    A.nCols - (v.transpose * A.transpose*A * v)(0)(0)
  }

  def muBar(A: Matrix): Vector[SafeLong] = {
    for (s <- spinStructures(A)) yield {
      muBar(A, s)
    }
  }

  /**  Enumerate all characteristic sublinks.
    *  Assume X^4 is given by only 2 handle attachments, with intersection form Q.
    *  Then the spin structure on bdry X <-> characteristic sublink.
    *  Let V = vertex set = set of all 2-handles
    *  S subset V is a characteristic sublink if:
    *    Q(sum_{s in S} s, x) = Q(x,x) (mod 2) for all x.
    * 
    *  @return Vector of v's given as row vectors
    */
  def charSublinks(Q: Matrix): Vector[Vector[SafeLong]] = {
    // Find v such that the following holds mod 2:
    //  e_i^t Q v = e_i^t Q e_i for all i
    //  equiv: Q_i v = Q_ii for all i (Q_i means ith row)
    // So Q v = {Q_ii}_i.

    val mats = Q.extendedSmithForm
    val D = mats._1
    val L = mats._2
    val R = mats._3
    //assert(D == L*Q*R)
    // D = L Q R.
    // So D (R^-1 v) = LQR (R^-1 v) = L (Q_11, ..., Q_nn)^t.
    // We solve for x = R^-1 v, then recover v.
    val n = Q.nCols
    val char = Matrix(Vector((0 until n).toVector.map(i => Q(i)(i)))).transpose
    val Lchar = L*char
    // Solving Dx = Lchar for x (with Z_2 coeffs).
    val Ddiag = D.diagonalElements
    val possCoeffs =
      for (i <- (0 until n).toVector) yield {
        if (Ddiag(i) % 2 == 0) {
          if (abs(Lchar.mat(i)(0)) % 2 == 0) {
            Vector(0,1)
          } else Vector()
        } else {
          if (abs(Lchar.mat(i)(0)) % 2 == 1)
            Vector(1)
          else
            Vector(0)
        }
      }

    def sequence[A](as: Vector[Vector[A]]): Vector[Vector[A]] = as match {
      case Vector() => Vector(Vector())
      case b +: cs =>
        for (x <- b;
          ys <- sequence(cs))
        yield (x +: ys)
    }

    val xs = sequence(possCoeffs)
    val vs = xs.map(s => (R*Matrix(Vector(s)).transpose).map(abs(_) % 2))
    vs.map(_.transpose.mat(0))
  }

}
