
package ahmad.hfhomology

import spire.implicits._
import spire.math._
import scala.annotation.tailrec
import spire.algebra.Field
import spire.algebra.Order

// Matrix over a field F.
case class FieldMatrix[F: Field](mat: Vector[Vector[F]]) {
  // TODO: make sure every row is the same size
  val nRows = mat.length
  val nCols = if (mat.length > 0) mat(0).length else 0

  def transpose: FieldMatrix[F] = FieldMatrix(
    for (i <- 0 until nCols toVector)
    yield (0 until nRows).toVector.map(mat(_)(i))
  )

  
  def rowSwitch(i: Int, j: Int): FieldMatrix[F] = FieldMatrix(
    (0 until nRows).toVector.map { k =>
      if (k == i) mat(j)
      else if (k == j) mat(i)
      else mat(k)
    }
  )

  def addMultiple(c: F, i: Int, j: Int): FieldMatrix[F] = FieldMatrix(
    // row j -> c*(row i) + (row j)
    (0 until nRows).toVector.map { k =>
      if (k == j) mat(i).zip(mat(j)).map(x => c*x._1 + x._2)
      else mat(k)
    }
  )


  def scaleRow(c: F, i: Int): FieldMatrix[F] = FieldMatrix(
    (0 until nRows).toVector.map { k =>
      if (k == i) mat(i).map(c*_)
      else mat(k)
    }
  )

  def multiply(m: FieldMatrix[F]): FieldMatrix[F] = {
    assert(this.nCols == m.nRows, s"Can't multiply ${nRows} x ${nCols} with ${m.nRows}x${m.nCols}")
    //val mt = m.transpose
    var total = implicitly[Field[F]].zero
    FieldMatrix(
      for (i <- 0 until nRows toVector) yield
        for (j <- 0 until m.nCols toVector) yield {
          //mat(i).zip(mt.mat(j)).map(x => x._1 * x._2).qsum
          
          total = implicitly[Field[F]].zero
          for (k <- 0 until nCols) {
            total += mat(i)(k) * m.mat(k)(j)
          }
          total
        }
    )
  }

  def *(m: FieldMatrix[F]) = multiply(m)

  override def toString: String =
    "{" + mat.map(v => "{" + v.mkString(",") + "}").mkString(",") + "}"

  /**
    * Puts matrix into row reduced echelon form by row operations.
    * Assumes operations are exact, don't use with floating point operations
    * (may lead to inaccuracy).
    */
  @tailrec
  final def rowReducedExact(p: Int = 0): FieldMatrix[F] = {
   // p denotes the pivot row
    val A = mat
    if (p >= min(nCols, nRows)) this

    else if (A(p)(p) == 0) {
      //make sure pivot is non-zero
      //search rows for non-zero entry
      (p+1 until nRows).find(A(_)(p) != 0) match {
        case Some(j) => rowSwitch(p, j).rowReducedExact(p)
        case None => this.rowReducedExact(p + 1)
      }
    } else if (A(p)(p) != 1) {
      scaleRow(1/A(p)(p), p).rowReducedExact(p) // scale it to 1
    } else {
      (0 until nRows).find(i => i != p && A(i)(p) != 0) match {
        case Some(j) => { // found a row with non-zero entry below
          val c = A(j)(p) / A(p)(p) // in fact A(p)(p) should be 1 by this point
          addMultiple(-1*c, p, j).rowReducedExact(p)
        }
        case None => {
          rowReducedExact(p + 1)
        }
      }
    }
  }

  /**
    * Puts matrix into row reduced echelon form by row operations.
    * Tries to choose largest pivot in column at each stage.
    */
  @tailrec
  final def rowReduced(tol: F, p: Int = 0)(implicit ord: Order[F]): FieldMatrix[F] = {
   // p denotes the pivot row
    val A = mat
    if (p >= min(nCols, nRows)) this

    else if (A(p)(p).abs < tol) {
      //make sure pivot is non-zero
      //search rows for non-zero entry
      (p+1 until nRows).find(A(_)(p).abs >= tol) match {
        case Some(j) => rowSwitch(p, j).rowReduced(tol, p)
        case None => this.rowReduced(tol, p + 1)
      }
    } else if ((p until nRows).exists(i => A(i)(p).abs > A(p)(p).abs)) {
      (p until nRows).find(i => A(i)(p).abs > A(p)(p).abs) match {
        case Some(i) => rowSwitch(p, i).rowReduced(tol, p)
        case None => throw new Exception("Can't reach here.")
      }
    } else if ((A(p)(p)-1).abs > tol) {
      scaleRow(1/A(p)(p), p).rowReduced(tol, p) // scale it to 1
    } else {
      (0 until nRows).find(i => i != p && A(i)(p).abs > tol) match {
        case Some(j) => { // found a row with non-zero entry below
          val c = A(j)(p) / A(p)(p) // in fact A(p)(p) should be 1 by this point
          addMultiple(-1*c, p, j).rowReduced(tol, p)
        }
        case None => {
          rowReduced(tol, p + 1)
        }
      }
    }
  }

  /**
    *  Adjoins matrix `m` to the right of `this`.
    *  [`this` | `m`].
    */
  def adjoin(m: FieldMatrix[F]): FieldMatrix[F] = {
    require(this.nRows == m.nRows, "Can't adjoin matrices, incompatible dimensions.")
    val cols = this.nCols + m.nCols
    val rows = this.nRows
    FieldMatrix.fromFunction(rows, cols, {
      case (i, j) if j < nCols => this(i)(j)
      case (i, j) => m(i)(j - nCols)
    })
  }

  /**
    * this = [`A`|`B`] returns (A, B), where A has `cols` columns.
    */
  def unadjoin(cols: Int): (FieldMatrix[F], FieldMatrix[F]) = {
    val left = FieldMatrix.fromFunction(nRows, cols, (i, j) => this(i)(j))
    val right = FieldMatrix.fromFunction(nRows, nCols - cols, (i, j) => this(i)(j + cols))
    (left, right)
  }

  def apply(i: Int) = mat(i)


  // Let A = this.
  // Solves A.x = b for x, assuming solution is unique.
  // This is only accurate for exact Fields (not floating point).
  def solveExact(b: FieldMatrix[F]): Either[String, FieldMatrix[F]] = {
    if (b.nRows != this.nRows) {
      Left(s"Incompatible dimensions: b has ${b.nRows} rows, but A has ${this.nRows} rows.")
    } else if (this.nCols > this.nRows) {
      Left("A given has more columns than rows: infinite or no solutions.")
    } else {
      val adjoined = this.adjoin(b)
      val (reducedA, reducedb) = adjoined.rowReducedExact().unadjoin(nCols)
      if (!(0 until nCols).forall(i => reducedA(i)(i) == 1)) {
        Left("Infinitely many solutions.")
      } else {
        Right(reducedb)
      }
    }
  }

  def inverseExact: Either[String, FieldMatrix[F]] = {
    if (nCols != nRows) Left("Can't invert non-square FieldMatrix.")
    else solveExact(FieldMatrix.id(nCols))
  }

  // Let A = this.
  // Solves A.x = b for x, assuming solution is unique.
  // This is used for inexact fields i.e. Double
  def solveApprox(b: FieldMatrix[F], tol: F)(implicit ord: Order[F]
  ): Either[String, FieldMatrix[F]] = {
    if (b.nRows != this.nRows) {
      Left(s"Incompatible dimensions: b has ${b.nRows} rows, but A has ${this.nRows} rows.")
    } else if (this.nCols > this.nRows) {
      Left("A given has more columns than rows: infinite or no solutions.")
    } else {
      val adjoined = this.adjoin(b)
      val (reducedA, reducedb) = adjoined.rowReduced(tol).unadjoin(nCols)
      if (!(0 until nCols).forall(i => reducedA(i)(i) > 1-tol)) {
        Left(s"Infinitely many solutions for matrix:\n$this\nreduced to\n$reducedA")
      } else {
        Right(reducedb)
      }
    }
  }

  def inverseApprox(tol: F)(implicit ord: Order[F]): Either[String, FieldMatrix[F]] = {
    if (nCols != nRows) Left("Can't invert non-square FieldMatrix.")
    else solveApprox(FieldMatrix.id(nCols), tol)
  }

  /**
    * Adds `n` constant rows (constant = `c`) to `this`.
    */
  def addConstantRows(n: Int, c: F) =
    FieldMatrix(mat ++ Vector.fill(n)(Vector.fill(nCols)(c)))
  
}

object FieldMatrix {
  // n x n identity matrix
  
  def id[F: Field](n: Int): FieldMatrix[F] = {
    require(n >= 0, "Can't construct identity matrix of size " + n)

    FieldMatrix[F](
    (0 until n).toVector.map { i =>
      (0 until n).toVector.map { j =>
        if (i == j) implicitly[Field[F]].one else implicitly[Field[F]].zero
      }
    })
  }

  def fromFunction[F: Field](nRows: Int, nCols: Int, f: (Int, Int) => F) = FieldMatrix[F](
    (0 until nRows).toVector.map(i =>
      (0 until nCols).toVector.map(j => f(i, j))
    )
  )
}
