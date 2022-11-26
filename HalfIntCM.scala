
package ahmad.hfhomology


import spire.implicits._
import spire.math._

/** Let r = numer of verts in tree.
  * Coefficients must be in terms of e_0, ..., e_{r+1}.
  * cm2 = e_0 - e_1
  * cm1 = e_1 + sigma_1 e_2 + ... + sigma_r e_{r+1} where (sigma_1, ..., sigma_r) is a cm vector.
  * The half-integer changemaker lattice is given by <cm1, cm2>^perp in Z^(r+1).
  */
import IntersectionForm.Coeffs
case class HalfIntCM(tree: Tree[(Int, Coeffs)], cm1: Coeffs, cm2: Coeffs, h1: Int) {
  val r = cm1.length - 1

  /** Returns standard basis as a matrix of column (basis) vectors. 
    * See "Alternating knots with unknotting number one" McCoy, Section 2.2.
    */
  def stdBasis: Matrix = {
    val sigma: Vector[Int] = cm1.map(_._1).sorted.drop(1)
    val mat = Changemaker.stdBasis(sigma)
    // We add two more rows to the top of `mat`.
    // If an entry in first row of `mat` contains 2, then
    // change it to 1, and in new two rows make the two entries above 1, 1.
    Matrix.fromFunction(r+2, r, {
      case (0, 0) => 1
      case (1, 0) => 1
      case (2, 0) => -1
      case (_, 0) => 0
      case (i, j) if i < 2 => if (mat(0)(j-1) == 2) 1 else 0
      case (i, j) => if (mat(i-2)(j-1) == 2) 1 else mat(i-2)(j-1)
    })
  }

  def stdBasisRows = Matrix(stdBasis.transpose.mat.map(_.reverse))

  /** P_{V->Z} where Z = Z^(n+1) basis and V is vertex basis.
  */
  def vertexBasis: Matrix = {
    val labelledTree = tree.toLabelledTree
    val vertices: Vector[Coeffs] = labelledTree.vertices.sortBy(_._2).map(_._1._2) // sort by label
    val mat = vertices.map { v =>
      (0 until r+2).toVector.map(i => v.find(_._2 == i)
        .map(c => SafeLong(c._1))
        .getOrElse(SafeLong(0))
      )
    }
    Matrix(mat).transpose
  }

  def vertexBasisRows: Matrix = vertexBasis.transpose


  /** Change of basis matrix, each std changemaker lattice vector is written
    * in terms of the vertex basis of the tree (labelled in terms of tree.toLabelledTree)
    * as a column vector of this matrix.
    * The vertex basis is ordered by labels of tree.toLabelledTree
    */
  def cmBasisToVertexBasis: Matrix = {
    val psz = stdBasis // P_{S->Z}
    val pvz = vertexBasis // P_{V->Z}

    /** P_{V->Z}  *  P_{S->V} = P_{S->Z} solving for P_{S->V}.
      * (r+2)*r     r*r  = (r+2)*r  (dimensions)
      *
      * Let A be an (r+2)x(r+2) matrix with A P_{V->Z} = identity plus zero rows
      * Then P_{S->V} is the first r rows of A P_{S->Z}.
      */
    val (left, pzv) = pvz.adjoin(Matrix.id(r+2)).rowReduced().unadjoin(r)
    // left should now be the identity with a zero row adjoined
    require(left == Matrix.id(r).addZeroRows(2), s"Not invertible over Z: \n$left")
    val psv = pzv * psz // (n+1)x n matrix
    // last row of psv = A*P_{S->Z} must be a zero row.
    require(psv(r+1).forall {_ == 0}, "Last row must be zeros.")
    require(psv(r).forall {_ == 0}, "Second last row must be zeros.")
    psv.dropLastRows(2)
    //psv.slice(0, 0, psv.nCols, psv.nRows - 1)
  }

  def pretty: String = {
    def prettyCoeffs(coeffs: Coeffs): String = coeffs.map({
      case (1, m) => "+e_" + m
      case (-1, m) => "-e_" + m
      case (p, m) if p > 0 => "+" + p + "e_" + m
      case (p, m) => p + "e_" + m
    }).mkString(" ")

    val sigma = "sigma = " + prettyCoeffs(cm1)
    val rho = "rho = " + prettyCoeffs(cm2)
    
    tree.toString + sigma + "\r\n" + rho
  }

}

