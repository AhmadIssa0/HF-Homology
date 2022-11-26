
package ahmad.hfhomology

import spire.implicits._
import spire.math._

/** Coefficients must be in terms of e_0, ..., e_n, where n+1 = cm.length
  */
import IntersectionForm.Coeffs
case class Changemaker(tree: Tree[(Int, Coeffs)], cm: Coeffs, h1: Int) {
  /** P_{V->Z} where Z = Z^(n+1) basis and V is vertex basis.
    */
  def vertexBasis: Matrix = {
    val labelledTree = tree.toLabelledTree
    val vertices: Vector[Coeffs] = labelledTree.vertices.sortBy(_._2).map(_._1._2) // sort by label
    val mat = vertices.map { v =>
      (0 until cm.length).toVector.map(i => v.find(_._2 == i)
        .map(c => SafeLong(c._1))
        .getOrElse(SafeLong(0))
      )
    }
    Matrix(mat).transpose
  }

  def vertexBasisRows: Matrix = vertexBasis.transpose

  lazy val cmRaw = {
    cm.map(_._1)
  }

  /** Change of basis matrix, each std changemaker lattice vector is written
    * in terms of the vertex basis of the tree (labelled in terms of tree.toLabelledTree)
    * as a column vector of this matrix.
    * The vertex basis is ordered by labels of tree.toLabelledTree
    */
  def cmBasisToVertexBasis: Matrix = {
    val psz = Changemaker.stdBasis(cmRaw) // P_{S->Z}
    val pvz = vertexBasis
    val n = cm.length - 1
    /** P_{V->Z}  *  P_{S->V} = P_{S->Z} solving for P_{S->V}.
      * (n+1)*n     n*(n+1)  = n*n  (dimensions)
      *
      * Let A be an (n+1)x(n+1) matrix with A P_{V->Z} = identity plus zero rows
      * Then P_{S->V} is the first n rows of A P_{S->Z}.
      */
    val (left, pzv) = pvz.adjoin(Matrix.id(n+1)).rowReduced().unadjoin(n)
    // left should now be the identity with a zero row adjoined
    require(left == Matrix.id(n).addZeroRows(1), s"Not invertible over Z: \n$left")
    val psv = pzv * psz // (n+1)x n matrix
    // last row of psv = A*P_{S->Z} must be a zero row.
    require(psv(n).forall {_ == 0}, "Last row must be zeros.")
    psv.dropLastRows(1)
    //psv.slice(0, 0, psv.nCols, psv.nRows - 1)
  }


  // two the images of two v_i overlap at the central vertex of the tree?
  def overlapsAtCentral: Boolean = {
    val labelledTree = tree.toLabelledTree
    val centralVerts = labelledTree.filterVertices(tree => tree.subtrees.length > 2)
    val cVertLabels = centralVerts.map(v => v._2) // indexed from 0
    val p = cmBasisToVertexBasis
    //println(labelledTree)
    //println("Central verts: " + cVertLabels)
    //println(cmBasisToVertexBasis)
    cVertLabels.exists(i => p(i).map(n => if (n != 0) 1 else 0).sum > 1)
  }


  def cmBasis: Matrix = Changemaker.stdBasis(cmRaw)

  def isTight(index: Int) = {
    if (index == 0) false
    else cmRaw(index) > cmRaw.slice(0, index).sum
  }

  def breakableIndices: Vector[Int] = tightIndices.filter(i => isBreakable(i))

  // check if v_i is breakable
  def isBreakable(i: Int): Boolean = !Changemaker.breakTight(cmRaw, i).isEmpty

  def tightIndices: Vector[Int] = Changemaker.tightIndices(cmRaw)

  def hasTight: Boolean = !tightIndices.isEmpty


  /**
    * Adjacency matrix of pairing graph G^(S) where S = std changemaker basis.
    */
  def pairingGraph: Matrix = Changemaker.pairingGraph(cmRaw)

  def stdBasisRows: Matrix = Changemaker.stdBasisRows(cmRaw)


}


object Changemaker {
  type CMVector = Vector[Int]

  def tightIndices(cm: CMVector): Vector[Int] = {
    (1 until cm.length).toVector.filter(i => cm(i) > cm.slice(0, i).sum)
  }

  def stdBasisRows(cm: CMVector) =
    Matrix(stdBasis(cm).transpose.mat.map(_.reverse))

  /** Given a changemaker vector, 
    * returns the standard basis as a matrix
    * P_{S -> Z} where S is the standard basis, and Z = basis of Z^{n+1}, n = `cm`.length.
    * Hence, if v_1 = e_0 - e_1, then first column is (1, -1, 0, ..., 0).
    */
  def stdBasis(cm: CMVector) = {
    // Write m in terms of the changemaker coefficients
    // with largest index equal to i. Does this greedily.
    def express(m: Int, maxIndex: Int = cm.length-1): Vector[Int] = {
      //println(s"expressing $m in terms of $cm, i=$maxIndex")
      def loop(n: Int, i: Int = cm.length-1): Vector[Int] = {
        if (i < 0) {
          require(n == 0, s"Can't express quantity $n in terms of cm coeffs $cm, i=$i.")
          Vector()
        } else {
          if (cm(i) <= n) (loop(n-cm(i), i-1) :+ 1) else (loop(n, i-1) :+ 0)
        }
      }
      loop(m, maxIndex) ++ Vector.fill(cm.length - maxIndex - 1)(0)
    }

    def isTight(i: Int) = 
      i > 0 && cm(i) > cm.slice(0, i).sum

    val mat = 
      (1 until cm.length).toVector.map { i => // i for v_i
        val res =
        if (isTight(i)) {
          (2 +: Vector.fill(i-1)(1) :+ -1) ++ Vector.fill(cm.length - i - 1)(0)
        } else {
          express(cm(i), i-1).updated(i, -1)
        }
        res.map(SafeLong(_))
      }
    Matrix(mat).transpose
  }

  def isTight(cm: CMVector, i: Int) =
    i > 0 && cm(i) > cm.slice(0, i).sum

  /**
    * Adjacency matrix of pairing graph G^(S) where S = std changemaker basis.
    */
  def pairingGraph(cm: CMVector): Matrix = {
    pairingGraph(stdBasis(cm).transpose)
  }

  // basis should be given as row vectors
  def pairingGraph(basis: Matrix): Matrix = {
    val gs = basis
    def dot(v1: Vector[SafeLong], v2: Vector[SafeLong]) =
      (0 until v1.length).map(i => v1(i)*v2(i)).qsum

    Matrix.fromFunction(gs.nRows, gs.nRows, {
      case (i, j) if i == j => 0
      case (i, j) => if (dot(gs(i), gs(j)) != 0) 1 else 0
    })
  }
  /** Computes all possible changemaker vectors of norm `norm`,
    * in Z^n with n = `parts`.
    */
  def changemaker(norm: Int, parts: Int) = {
    def loop(
      rem: Int = norm - 1,
      lenOfRest: Int = parts - 1,
      curr: Vector[Int] = Vector(1)
    ): Vector[CMVector] = {
      if (rem == 0 && lenOfRest == 0) Vector(Vector())
        else if (lenOfRest <= 0 || rem <= 0) Vector()
      else {
        val n = min(sqrt(rem.toDouble).toInt, curr.sum + 1)
        for (
          i <- (curr.last to n).toVector;
          lst <- loop(rem - i*i, lenOfRest - 1, curr :+ i)
        ) yield (i +: lst)
      }
    }
    loop().map(1 +: _)
  }

  /** Suppose we have a changemaker lattice in Z^(n+1), with std basis S.
    * Suppose v_i = x + y, x.y = -1, |x| >= 3, |y| >= 3.
    * 
    * There are two forms x and y can take.
    * Form (1) requires n >= i + 2:
    * v_i = 0{2,}          -1 1{i-1}     2
    *   x = 0* 1  0* -1 0* -1 [0-1]{i-1} 1
    *   y = 0* -1 0*  1 0*  1 [0-1]{i-1} 1
    * 
    * v_i = 0  0 0  0 0 -1 1 1 1 1 1 2
    *   x = 0  1 0 -1 0 -1 1 0 1 0 0 1
    *   y = 0 -1 0  1 0  0 0 1 0 1 1 0
    * 
    * Here, coefficient of e_n is listed with n decreasing left to right.
    * y is in the span of S\v_i.
    * 
    * Form (2):
    * v_i = 0{2,}    -1 1{i-1}                           2
    *   x = 0{2,}    -1 1*  2   (0 or 1 at least one 0)  1
    *   y = 0*          0* -1   (0 or 1 at least one 1)  1. (Note at least one 1 or else |y| < 3).
    * 
    * v_i = 0 0 0 -1 1 1 1  1 1 1 1 1 1 2
    *   x = 0 0 0 -1 1 1 1  2 1 0 1 1 0 1
    *   y = 0 0 0  0 0 0 0 -1 0 1 0 0 1 1
    * 
    * Note that y in this second case is in the span of S\v_i.
    */
  def repeat(choice: Vector[Int], times: Int): Vector[Vector[Int]] = {
    assert(times >= 0)
    if (times == 0) Vector(Vector())
    else if (times > 0 && choice.isEmpty) Vector()
    else {
      repeat(choice, times-1).flatMap { tail =>
        choice.map(_ +: tail)
      }
    }
  }
  // cm has length n+1
  def xform1(i: Int, n: Int): Vector[Vector[Int]] = {
    if (i + 2 > n) Vector()
    else {
      val inners = repeat(Vector(0, 1), i-1)
      (0 until n-i).combinations(2).toVector.flatMap { case Vector(j, k) =>
        val left = Vector.fill(n-i)(0).updated(j, -1).updated(k, 1)
        inners.map(inner =>
          (1 +: inner :+ -1) ++ left
        )
      }
    }
  }

  def xform2(i: Int, n: Int): Vector[Vector[Int]] = {
    if (i <= 2) Vector()
    else {
      (0 until i-2).toVector.flatMap { j => // j is number of 1's between -1 and 2
        val inners = repeat(Vector(0,1), i-j-2).filter(_ contains 0)
        val ones = Vector.fill(j)(1)
        val zeros = Vector.fill(n-i)(0)
        inners.map(inner => (1 +: inner :+ 2) ++ (ones :+ -1) ++ zeros)
      }
    }
  }

  def dot(v1: Vector[Int], v2: Vector[Int]) = {
    assert(v1.length == v2.length)
    (0 until v1.length).map(i => v1(i)*v2(i)).sum
  }

  def subtract(v1: Vector[Int], v2: Vector[Int]) = {
    assert(v1.length == v2.length)
    (0 until v1.length).toVector.map(i => v1(i) - v2(i))
  }

  def add(v1: Vector[Int], v2: Vector[Int]) = {
    assert(v1.length == v2.length)
    (0 until v1.length).toVector.map(i => v1(i) + v2(i))
  }

  def inLattice(v: Vector[Int], cm: CMVector) = {
    require(v.length == cm.length)
    dot(v, cm) == 0
  }

  // i for v_i
  def tightVector(i: Int, n: Int): Vector[Int] = 
    (2 +: Vector.fill(i-1)(1) :+ -1) ++ Vector.fill(n - i)(0)

  // returns all (x, y) with v_i = x + y breakable form, with v_i tight.
  def breakTight(cm: CMVector, i: Int) = {
    require(i > 0 && i < cm.length && isTight(cm, i), s"i = $i, cm = $cm")
    val n = cm.length - 1
    val tight = tightVector(i, n)
    (xform1(i, n) /*++ xform2(i, n)*/)
      .filter(x => inLattice(x, cm))
      .map { x => 
        val y = subtract(tight, x)
        if (expressInStdBasis(cm, x)(i-1) == 0) (y, x) else (x, y)
      }
  }

  // Writes a vector v in L as a linear combination
  // of changemaker stdBasis vectors v_1, v_2, ...
  def expressInStdBasis(cm: CMVector, v: Vector[Int]) = {
    assert(cm.length == v.length && inLattice(v, cm))
    val basis = stdBasis(cm).transpose

    def loop(i: Int, rem: Vector[Int]): Vector[Int] = {
      if (i <= 0) Vector()
      else {
        val scaled = basis(i-1).map(n => (n * rem(i)).toInt)
        loop(i-1, add(rem, scaled)) :+ (-rem(i))
      }
    }
    loop(v.length - 1, v)
  }

}
