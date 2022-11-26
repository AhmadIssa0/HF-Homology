
package ahmad.hfhomology

import spire.implicits._
import spire.math._
import scala.annotation.tailrec

case class Matrix(mat: Vector[Vector[SafeLong]]) {
  // TODO: make sure every row is the same size
  val nRows = mat.length
  val nCols = if (mat.length > 0) mat(0).length else 0

  def dimensions = (nRows, nCols)

  def map(f: SafeLong => SafeLong): Matrix = {
    Matrix(mat.map(_.map(f(_))))
  }

  def columns: Vector[Matrix] = {
    this.transpose.mat.map(row => Matrix(Vector(row)).transpose)
  }

  def flatten: Vector[SafeLong] = 
    mat.foldLeft(Vector[SafeLong]())((p, row) => p ++ row)

  def diagonalElements =
    (0 until min(nRows, nCols)).toVector.map(i => mat(i)(i))

  def rowSwitch(i: Int, j: Int): Matrix = Matrix(
    (0 until nRows).toVector.map { k =>
      if (k == i) mat(j)
      else if (k == j) mat(i)
      else mat(k)
    }
  )

  /** Entrywise operation on two matrices.
    */
  def hadamard(that: Matrix, op: (SafeLong, SafeLong) => SafeLong): Matrix = {
    require(this.nRows == that.nRows && this.nCols == that.nCols)
    Matrix(
      (0 until nRows).toVector.map { i =>
        (0 until nCols).toVector.map { j =>
          op(this(i)(j), that(i)(j))
        }
      }
    )
  }

  def colSwitch(i: Int, j: Int): Matrix = Matrix(
    for (row <- mat) yield {
      (0 until row.length).toVector.map { k =>
        if (k == i) row(j)
        else if (k == j) row(i)
        else row(k)
      }
    }
  )

  def colAddMultiple(c: SafeLong, i: Int, j: Int): Matrix = Matrix(
    for (row <- mat) yield {
      (0 until row.length).toVector.map { k =>
        if (k == j) (row(j) + c*row(i))
        else row(k)
      }      
    }
  )


  def addMultiple(c: SafeLong, i: Int, j: Int): Matrix = Matrix(
    // row j -> c*(row i) + (row j)
    (0 until nRows).toVector.map { k =>
      if (k == j) mat(i).zip(mat(j)).map(x => c*x._1 + x._2)
      else mat(k)
    }
  )

  def scaleRow(c: SafeLong, i: Int): Matrix = Matrix(
    (0 until nRows).toVector.map { k =>
      if (k == i) mat(i).map(c*_)
      else mat(k)
    }
  )

  def scaleMatrix(c: SafeLong): Matrix = Matrix(
    mat.map(row => row.map(_ * c))
  )

  def *(c: SafeLong) = scaleMatrix(c)

  def add(that: Matrix) = hadamard(that, _ + _)

  def +(that: Matrix) = add(that)

  def -(that: Matrix) = {
    assert(this.nRows == that.nRows && this.nCols == that.nCols, "Can't subtract matrices of different sizes")
    add(that.map(entry => -entry))
  }

  override def toString: String =
    "{" + mat.map(v => "{" + v.mkString(",") + "}").mkString(",") + "}"

  def scaleCol(c: SafeLong, i: Int): Matrix = Matrix(
    for (row <- mat) yield {
      (0 until row.length).toVector.map { k =>
        if (k == i) c*row(k)
        else row(k)
      }
    }
  )

  def replaceRow(i: Int, row: Vector[SafeLong]) =
    Matrix(mat.updated(i, row))

  def transpose: Matrix = Matrix(
    for (i <- 0 until nCols toVector)
    yield (0 until nRows).toVector.map(mat(_)(i))
  )
  
  def multiply(m: Matrix): Matrix = {
    val mt = m.transpose
    Matrix(
      for (i <- 0 until nRows toVector) yield
        for (j <- 0 until mt.nRows toVector)
        yield mat(i).zip(mt.mat(j)).map(x => x._1 * x._2).qsum
    )
  }

  def *(m: Matrix) = multiply(m)

  /**
    *  Adjoins matrix `m` to the right of `this`.
    *  [`this` | `m`].
    */
  def adjoin(m: Matrix): Matrix = {
    require(this.nRows == m.nRows, "Can't adjoin matrices, incompatible dimensions.")
    val cols = this.nCols + m.nCols
    val rows = this.nRows
    Matrix.fromFunction(rows, cols, {
      case (i, j) if j < nCols => this(i)(j)
      case (i, j) => m(i)(j - nCols)
    })
  }

  /**
    * this = [`A`|`B`] returns (A, B), where A has `cols` columns.
    */
  def unadjoin(cols: Int): (Matrix, Matrix) = {
    val left = Matrix.fromFunction(nRows, cols, (i, j) => this(i)(j))
    val right = Matrix.fromFunction(nRows, nCols - cols, (i, j) => this(i)(j + cols))
    (left, right)
  }

  /**
    * Adds `n` zero rows to `this`.
    */
  def addZeroRows(n: Int) = Matrix(mat ++ Vector.fill(n)(Vector.fill(nCols)(SafeLong(0))))

  def adjoinRow(row: Vector[SafeLong]) = {
    assert(row.length == nCols)
    Matrix(mat :+ row)
  }

  /**
    *  A submatrix with top-left entry with index of `this` given by
    *  (x1, y1), bottom-right is (x2-1, y2-1).
    */
  def slice(x1: Int, y1: Int, x2: Int, y2: Int): Matrix = {
    Matrix.fromFunction(x2 - x1, y2 - y1, (i, j) => this(x1 + i)(y1 + j))
  }

  def switchHalves: Matrix = Matrix(
    (0 until nRows).toVector.map { i =>
      mat((i + nRows/2) % nRows)
    }
  )

  /**
    *  Drop last `n` rows of the matrix.
    */
  def dropLastRows(n: Int): Matrix = {
    assert(nRows - n >= 0)
    slice(0, 0, nRows - n, nCols)
  }

  /**
    * Deletes row i and column j.
    */
  def minor(i: Int, j: Int): Matrix = Matrix.fromFunction(nRows - 1, nCols - 1, {
    case (s, t) if s < i && t < j => this(s)(t)
    case (s, t) if s >= i && t < j => this(s+1)(t)
    case (s, t) if s < i && t >= j => this(s)(t+1)
    case (s, t) => this(s+1)(t+1)
  })

  def nullity: Int = {
    val rref = rowReduced()
    rref.nCols - rref.mat.map(row => if (row.exists(_ != 0)) 1 else 0).sum
  }

  /**
    * Puts matrix into row reduced echelon form by row operations.
    * Note working with integer matrices, so doesn't perform division.
    */
  @tailrec
  final def rowReduced(p: Int = 0): Matrix = {
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
    } else if (A(p)(p) < 0) {
      scaleRow(-1, p).rowReduced(p)
    } else {
      (p+1 until nRows).find(A(_)(p) != 0) match {
        case Some(j) => {
          if (A(j)(p) < 0) scaleRow(-1, j).rowReduced(p)
          else if (A(j)(p) < A(p)(p)) {
            rowSwitch(j, p).rowReduced(p)
          } else {
            val c = A(j)(p) / A(p)(p)
            addMultiple(-1*c, p, j).rowReduced(p)
          }
        }
        case None => {
          (0 until p).find(i => A(i)(p) != 0 && A(i)(p) % A(p)(p) == 0) match {
            case Some(i) => {
              val c = A(i)(p) / A(p)(p)
              addMultiple(-1*c, p, i).rowReduced(p)
            }
            case None => rowReduced(p + 1)
          }
        }
      }
    }
  }

  /**
    * Puts matrix into row reduced echelon form by row operations.
    * Note working with integer matrices, so doesn't perform division.
    * Returns (D, L), where L A = D, where A = this matrix 
    */
  def extendedRowReduced(p: Int = 0): (Matrix, Matrix) = {
    val id = Matrix.id(this.nRows)
    @tailrec
    def loop(p: Int = 0, currMat: Matrix, L: Matrix): (Matrix, Matrix) = {
      // p denotes the pivot row
      val A = currMat.mat
      if (p >= min(nCols, nRows)) (currMat, L)
      else if (A(p)(p) == 0) {
        //make sure pivot is non-zero
        //search rows for non-zero entry
        (p+1 until nRows).find(A(_)(p) != 0) match {
          case Some(j) => loop(p, currMat.rowSwitch(p, j), L.rowSwitch(p, j))
          case None => loop(p+1, currMat, L)
        }
      } else if (A(p)(p) < 0) {
        loop(p, currMat.scaleRow(-1, p), L.scaleRow(-1, p))
        //scaleRow(-1, p).rowReduced(p)
      } else {
        (p+1 until nRows).find(A(_)(p) != 0) match {
          case Some(j) => {
            if (A(j)(p) < 0) loop(p, currMat.scaleRow(-1, j), L.scaleRow(-1, j))//scaleRow(-1, j).rowReduced(p)
            else if (A(j)(p) < A(p)(p)) {
              loop(p, currMat.rowSwitch(j, p), L.rowSwitch(j, p))
              //rowSwitch(j, p).rowReduced(p)
            } else {
              val c = A(j)(p) / A(p)(p)
              loop(p, currMat.addMultiple(-1*c, p, j), L.addMultiple(-1*c, p, j))
              //addMultiple(-1*c, p, j).rowReduced(p)
            }
          }
          case None => {
            (0 until p).find(i => A(i)(p) != 0 && A(i)(p) % A(p)(p) == 0) match {
              case Some(i) => {
                val c = A(i)(p) / A(p)(p)
                loop(p, currMat.addMultiple(-1*c, p, i), L.addMultiple(-1*c, p, i))
                //addMultiple(-1*c, p, i).rowReduced(p)
              }
              case None => loop(p+1, currMat, L) //rowReduced(p + 1)
            }
          }
        }
      }
    }

    loop(0, this, id)
  }

  def apply(i: Int) = mat(i)


  def inverse = {
    assert(absDet == 1) // We only inverse det 1 matrices
    /** Let A be this matrix.
      * [Id | 0] = L [A | Id] by row reduction
      * L is the inverse of A
      */
    extendedRowReduced()._2
  }


  /**  Let A be this matrix.
    *  @returns (D, L, R) where D is the smith normal form of A and D = L A R.
    */
  def extendedSmithForm: (Matrix, Matrix, Matrix) = {
    // p is pivot
    @tailrec
    def loop(p: Int, A: Matrix, L: Matrix, R: Matrix): (Matrix, Matrix, Matrix) = {
      if (p >= min(nCols, nRows)) {
        // We now have a "diagonal" matrix. Need to ensure d_i | d_{i+1} for all i,
        // where d_j is the jth diagonal entry.

        val n = min(nCols, nRows)
        // Ensure any d_i = 0 are the final diagonal entries.
          (0 until n-1).find(i =>
            A(i)(i) == 0 && (i+1 until n).exists { j => A(j)(j) != 0 }) match {
          case Some(i) => {
            val j = (i+1 until n).find(j => A(j)(j) != 0).get
            // Switch columns i and j, then rows i and j
            loop(p, A.colSwitch(i, j).rowSwitch(i, j),
                   L.rowSwitch(i, j), R.colSwitch(i, j))           
          }
          case None => { // all zero diagonal entries are now last
            (0 until n-1).find(i => (A(i+1)(i+1) % A(i)(i)) != 0) match {
              case Some(i) => {
                // add row i+1 to row i then repeat smith normal form.
                loop(i, A.addMultiple(1, i+1, i), L.addMultiple(1, i+1, i), R)
              }
              case None => (A, L, R)
            }
          }
        }
      } else if (A(p)(p) == 0) {
        //make sure pivot is non-zero
        //search rows for non-zero entry
        (p+1 until nRows).find(A(_)(p) != 0) match {
          case Some(j) => loop(p, A.rowSwitch(p, j), L.rowSwitch(p, j), R)
          case None => {
            // search columns
            (p+1 until nCols).find(A(p)(_) != 0) match {
              case Some(j) => loop(p, A.colSwitch(p, j), L, R.colSwitch(p, j))
              case None => loop(p+1, A, L, R)
            }
          }
        }
      } else if (A(p)(p) < 0) {
        loop(p, A.scaleRow(-1, p), L.scaleRow(-1, p), R)
      } else {
        (p+1 until nRows).find(A(_)(p) != 0) match {
          case Some(j) => {
            if (A(j)(p) < 0) loop(p, A.scaleRow(-1, j), L.scaleRow(-1, j), R)
            else if (A(j)(p) < A(p)(p)) {
              loop(p, A.rowSwitch(j, p), L.rowSwitch(j, p), R)
            } else {
              val c = A(j)(p) / A(p)(p)
              loop(p, A.addMultiple(-1*c, p, j), L.addMultiple(-1*c, p, j), R)
            }
          }
          case None => (p+1 until nCols).find(A(p)(_) != 0) match {
            case Some(j) => {
              if (A(p)(j) < 0) loop(p, A.scaleCol(-1, j), L, R.scaleCol(-1, j))
              else if (A(p)(j) < A(p)(p)) {
                loop(p, A.colSwitch(j, p), L, R.colSwitch(j, p))
              } else {
                val c = A(p)(j) / A(p)(p)
                loop(p, A.colAddMultiple(-1*c, p, j), L, R.colAddMultiple(-1*c, p, j))
              }
            }
            case None => loop(p + 1, A, L, R)
          }
        }
      }
    }
    loop(0, this, Matrix.id(nRows), Matrix.id(nCols))
  }


  @tailrec
  final def smithNormalForm(p: Int = 0): Matrix = {
    // p denotes the pivot row/col
    val A = mat
    if (p >= min(nCols, nRows)) {
      // We now have a "diagonal" matrix. Need to ensure d_i | d_{i+1} for all i,
      // where d_j is the jth diagonal entry.

      val n = min(nCols, nRows)
      // Ensure any d_i = 0 are the final diagonal entries.
        (0 until n-1).find(i =>
          A(i)(i) == 0 && (i+1 until n).exists { j => A(j)(j) != 0 }) match {
        case Some(i) => {
          val j = (i+1 until n).find(j => A(j)(j) != 0).get
          // Switch columns i and j, then rows i and j
          colSwitch(i, j).rowSwitch(i, j).smithNormalForm(p)
        }
        case None => { // all zero diagonal entries are now last
          (0 until n-1).find(i => (A(i+1)(i+1) % A(i)(i)) != 0) match {
            case Some(i) => {
              // add row i+1 to row i then repeat smith normal form.
              addMultiple(1, i + 1, i).smithNormalForm(i)
            }
            case None => this
          }
        }
      }
    } else if (A(p)(p) == 0) {
      //make sure pivot is non-zero
      //search rows for non-zero entry
      (p+1 until nRows).find(A(_)(p) != 0) match {
        case Some(j) => rowSwitch(p, j).smithNormalForm(p)
        case None => {
          // search columns
          (p+1 until nCols).find(A(p)(_) != 0) match {
            case Some(j) => colSwitch(p, j).smithNormalForm(p)
            case None => smithNormalForm(p + 1)
          }
        }
      }
    } else if (A(p)(p) < 0) {
      scaleRow(-1, p).smithNormalForm(p)
    } else {
      (p+1 until nRows).find(A(_)(p) != 0) match {
        case Some(j) => {
          if (A(j)(p) < 0) scaleRow(-1, j).smithNormalForm(p)
          else if (A(j)(p) < A(p)(p)) {
            rowSwitch(j, p).smithNormalForm(p)
          } else {
            val c = A(j)(p) / A(p)(p)
            addMultiple(-1*c, p, j).smithNormalForm(p)
          }
        }
        case None => (p+1 until nCols).find(A(p)(_) != 0) match {
          case Some(j) => {
            if (A(p)(j) < 0) scaleCol(-1, j).smithNormalForm(p)
            else if (A(p)(j) < A(p)(p)) {
              colSwitch(j, p).smithNormalForm(p)
            } else {
              val c = A(p)(j) / A(p)(p)
              colAddMultiple(-1*c, p, j).smithNormalForm(p)
            }
          }
          case None => smithNormalForm(p + 1)
        }
      }
    }
  }

  // Absolute value of determinant
  def absDet: SafeLong = abs(invariantFactors.qproduct)

  def invariantFactors: Vector[SafeLong] = {
    val smith = smithNormalForm()
    val invFactors = (0 until min(smith.nCols, smith.nRows)).toVector.map(i => smith.mat(i)(i))
    // 0 rows give Z factors
    val numZFactors = smith.nRows - min(smith.nCols, smith.nRows)
    // Invariant factors of 1 give Z/Z = 0 factor in homology, discard unless
    // we have a Z-homology sphere, then leave one factor.
    val numOnes = min(invFactors.takeWhile(_ == 1).length, invFactors.length + numZFactors - 1)
    invFactors.drop(numOnes) ++ Vector.fill(numZFactors)(SafeLong(0))
  }

  def isSurjective: Boolean = 
    nRows <= nCols && invariantFactors.forall(_ == 1)

  def toIntVector: Vector[Vector[Int]] =
    mat.map(_.map(_.toInt))

  def toRatMatrix = RatMatrix(mat.map(_.map(_.toRational)))
  
}

object Matrix {
  // n x n identity matrix
  def id(n: Int): Matrix = {
    require(n >= 0, "Can't construct identity matrix of size " + n)

    Matrix(
    (0 until n).toVector.map { i =>
      (0 until n).toVector.map { j =>
        if (i == j) SafeLong(1) else SafeLong(0)
      }
    })
  }

  def zero(rows: Int, cols: Int): Matrix = {
    Matrix(Vector.fill(rows)(Vector.fill(cols)(SafeLong(0))))
  }

  // DummyImplicit used to work around type erasure
  def apply(mat: Vector[Vector[Int]])(implicit d: DummyImplicit): Matrix = {
    Matrix(mat.map(_.map(SafeLong(_))))
  }

  def fromFunction(nRows: Int, nCols: Int, f: (Int, Int) => SafeLong) = Matrix(
    (0 until nRows).toVector.map(i =>
      (0 until nCols).toVector.map(j => f(i, j))
    )
  )
}
