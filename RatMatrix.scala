
package ahmad.hfhomology

import spire.implicits._
import spire.math._
import scala.annotation.tailrec

case class RatMatrix(mat: Vector[Vector[Rational]]) {
  // TODO: make sure every row is the same size
  val nRows = mat.length
  val nCols = if (mat.length > 0) mat(0).length else 0

  def transpose: RatMatrix = RatMatrix(
    for (i <- 0 until nCols toVector)
    yield (0 until nRows).toVector.map(mat(_)(i))
  )

  def rowSwitch(i: Int, j: Int): RatMatrix = RatMatrix(
    (0 until nRows).toVector.map { k =>
      if (k == i) mat(j)
      else if (k == j) mat(i)
      else mat(k)
    }
  )

  def addMultiple(c: Rational, i: Int, j: Int): RatMatrix = RatMatrix(
    // row j -> c*(row i) + (row j)
    (0 until nRows).toVector.map { k =>
      if (k == j) mat(i).zip(mat(j)).map(x => c*x._1 + x._2)
      else mat(k)
    }
  )


  def scaleRow(c: Rational, i: Int): RatMatrix = RatMatrix(
    (0 until nRows).toVector.map { k =>
      if (k == i) mat(i).map(c*_)
      else mat(k)
    }
  )

  def multiply(m: RatMatrix): RatMatrix = {
    val mt = m.transpose
    RatMatrix(
      for (i <- 0 until nRows toVector) yield
        for (j <- 0 until mt.nRows toVector)
        yield mat(i).zip(mt.mat(j)).map(x => x._1 * x._2).qsum
    )
  }

  def *(m: RatMatrix) = multiply(m)

  override def toString: String =
    "{" + mat.map(v => "{" + v.mkString(",") + "}").mkString(",") + "}"

  /**
    * Puts matrix into row reduced echelon form by row operations.
    *
    */
  @tailrec
  final def rowReduced(p: Int = 0): RatMatrix = {
   // p denotes the pivot row
    val A = mat
    if (p >= min(nCols, nRows)) this
    else if (A(p)(p) == 0) {
      //make sure pivot is non-zero
      //search rows for non-zero entry
      (p+1 until nRows).find(A(_)(p) != 0) match {
        case Some(j) => rowSwitch(p, j).rowReduced(p)
        case None => this.rowReduced(p + 1)
      }
    } else if (A(p)(p) != 1) {
      scaleRow(1/A(p)(p), p).rowReduced(p) // scale it to 1
    } else {
      (0 until nRows).find(i => i != p && A(i)(p) != 0) match {
        case Some(j) => { // found a row with non-zero entry below
          val c = A(j)(p) / A(p)(p) // in fact A(p)(p) should be 1 by this point
          addMultiple(-1*c, p, j).rowReduced(p)
        }
        case None => {
          rowReduced(p + 1)
        }
      }
    }
  }


  /**
    *  Adjoins matrix `m` to the right of `this`.
    *  [`this` | `m`].
    */
  def adjoin(m: RatMatrix): RatMatrix = {
    require(this.nRows == m.nRows, "Can't adjoin matrices, incompatible dimensions.")
    val cols = this.nCols + m.nCols
    val rows = this.nRows
    RatMatrix.fromFunction(rows, cols, {
      case (i, j) if j < nCols => this(i)(j)
      case (i, j) => m(i)(j - nCols)
    })
  }

  /**
    * this = [`A`|`B`] returns (A, B), where A has `cols` columns.
    */
  def unadjoin(cols: Int): (RatMatrix, RatMatrix) = {
    val left = RatMatrix.fromFunction(nRows, cols, (i, j) => this(i)(j))
    val right = RatMatrix.fromFunction(nRows, nCols - cols, (i, j) => this(i)(j + cols))
    (left, right)
  }

  def apply(i: Int) = mat(i)


  // Let A = this.
  // Solves A.x = b for x, assuming solution is unique.
  def solve(b: RatMatrix): Either[String, RatMatrix] = {
    if (b.nRows != this.nRows) {
      Left(s"Incompatible dimensions: b has ${b.nRows} rows, but A has ${this.nRows} rows.")
    } else if (this.nCols > this.nRows) {
      Left("A given has more columns than rows: infinite or no solutions.")
    } else {
      val adjoined = this.adjoin(b)
      val (reducedA, reducedb) = adjoined.rowReduced().unadjoin(nCols)
      if (!(0 until nCols).forall(i => reducedA(i)(i) == 1)) {
        Left("Infinitely many solutions.")
      } else {
        Right(reducedb)
      }
    }
  }

  def inverse: Either[String, RatMatrix] = {
    if (nCols != nRows) Left("Can't invert non-square RatMatrix.")
    else solve(RatMatrix.id(nCols))
  }

  /**
    * Adds `n` constant rows (constant = `c`) to `this`.
    */
  def addConstantRows(n: Int, c: Rational) =
    RatMatrix(mat ++ Vector.fill(n)(Vector.fill(nCols)(c)))
}

object RatMatrix {
  // n x n identity matrix
  def id(n: Int): RatMatrix = {
    require(n >= 0, "Can't construct identity matrix of size " + n)

    RatMatrix(
    (0 until n).toVector.map { i =>
      (0 until n).toVector.map { j =>
        if (i == j) Rational(1) else Rational(0)
      }
    })
  }

  def fromFunction(nRows: Int, nCols: Int, f: (Int, Int) => Rational) = RatMatrix(
    (0 until nRows).toVector.map(i =>
      (0 until nCols).toVector.map(j => f(i, j))
    )
  )
}
