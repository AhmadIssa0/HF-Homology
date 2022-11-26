
package ahmad.hfhomology

import spire.implicits._
import spire.math._

object Graph {
  def degrees(adj: Matrix): Vector[SafeLong] =
    adj.mat.map(_.qsum)

  def laplaceMatrix(adj: Matrix): Matrix = {
    val degs = degrees(adj)
    Matrix.fromFunction(adj.nRows, adj.nCols, {
      case (i, j) if i == j => degs(i)
      case (i, j) => -adj(i)(j)
    })
  }

  def numberOfComponents(adj: Matrix): Int = {
    laplaceMatrix(adj).nullity
  }

  def removeVertex(adj: Matrix, i: Int): Matrix = adj.minor(i, i)

  def adjacentVerts(adj: Matrix, i: Int): Vector[Int] =
    (0 until adj.nRows).toVector.filter(j => j != i && adj(i)(j) != 0)

  def isClaw(adj: Matrix, i: Int): Boolean = {
    val adjVerts = adjacentVerts(adj, i)
    adjVerts.combinations(2).forall({
      case Vector(a, b) => adj(a)(b) == 0
    })
  }
}
