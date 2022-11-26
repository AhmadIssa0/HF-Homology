 
package ahmad.hfhomology

import spire.implicits._
import spire.math._

/**
  * @param adjacency adjacency(v) should be the CCW vertices adjacent to v.
  *                  We have a pair (a, i), where a is the vertex label and i
  *                  is a unique marker for the edge.
  */
case class PlanarGraph[A](adjacency: Map[A, Vector[(A, Int)]]) {
  type Edge = (A, A, Int)

  def directedEdges: Vector[Edge] = {
    adjacency.keys.toVector.flatMap({ v =>
      adjacency(v).map({ case (v2, i) => (v, v2, i) })
    })
  }

  def rotateCCW(e: Edge, notches: Int = 1): Edge = {
    val (vTail, vHead, marker) = e
    val adjVerts = adjacency(vTail)
    val n = adjVerts.length
    adjVerts.indexOf((vHead, marker)) match {
      case -1 => throw new IllegalArgumentException(s"Edge: $e is not a valid edge.")
      case i => {
        val iNext = ((i + notches) % n + n) % n
        val (v, marker2) = adjVerts(iNext)
        (vTail, v, marker2)
      }
    }
  }


  /**
    * Returns edges of the dual face to the right of directed edge `edge`.
    * Edges are given in CCW order (but oriented CW)
    */
  def dualFaceEdges(edge: Edge): Vector[Edge] = {
    def nextEdge(e: Edge) = {
      val (v1, v2, marker) = rotateCCW(e, notches = -1) // CW
      (v2, v1, marker)
    }

    def loop(currEdge: Edge, edges: Vector[Edge]): Vector[Edge] = {
      if (!edges.isEmpty && currEdge == edges.head) edges
      else loop(nextEdge(currEdge), edges :+ currEdge)
    }

    val ccwEdges = loop(edge, Vector())
    ccwEdges
  }


  def dualGraph: PlanarGraph[Int] = {
    //println(s"orig graph: $this")
    type Face = Vector[Edge]

    def dualFaces(edgesRem: Vector[Edge],
      faces: Vector[Face]
    ): Vector[Face] = edgesRem match {
      case Vector() => faces
      case e +: v => {
        val face = dualFaceEdges(e)
        dualFaces(edgesRem.filter(e => !face.contains(e)), faces :+ face)
      }
    }

    val faces = dualFaces(directedEdges, Vector())
    //println(s"dual faces: $faces")
    val pg: Vector[(Int, Vector[(Int, Int)])] = 
      (0 until faces.length).toVector.map({ i =>
        val adjVerts =
          faces(i).map({ e => (faces.indexWhere(_.contains((e._2, e._1, e._3))), e._3) })
        (i, adjVerts)
      })
    PlanarGraph(Map(pg: _*))
  }

  def degree(vert: A): Int = adjacency(vert).length

  def toIntersectionForm: IntersectionForm = {
    if (adjacency.keys.isEmpty) {
      IntersectionForm(Vector())
    } else {
      // Remove a vertex of highest degree
      //println(s"Degree vert removing: ${adjacency.keys.map(degree _).max}")
      toIntersectionForm(adjacency.keys.maxBy(degree _))
    }
  }


  // Neg definite.
  def toIntersectionForm(keyToDelete: A): IntersectionForm = {
    val keys = adjacency.keys.toVector
    val n = keys.length
    //println(s"num keys: $n")
    val mat =
      (0 until n).toVector.map(a =>
        (0 until n).toVector.map(b => (a, b) match {
          case (i, j) if i == j => -adjacency(keys(i)).length
          case (i, j) => adjacency(keys(i)).count(_._1 == keys(j))
        }))
    val i = keys.indexOf(keyToDelete)
    //println(s"mat=$mat")
    //println(s"to remove index: $i")
    assert(i != -1)
    val rowRemoved = mat.slice(0, i) ++ mat.slice(i+1, n)
    IntersectionForm(rowRemoved.map(row => row.slice(0, i) ++ row.slice(i+1, n)))
  }
}

object PlanarGraph {

}
