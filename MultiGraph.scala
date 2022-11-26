
package ahmad.hfhomology

import spire.implicits._
import spire.math._

case class EntryPoint(tag: VertexTag, index: Int) {
  override def toString = s"E($tag, $index)"

}

case class MultiVertex(tag: String, adjacent: Vector[EntryPoint]) {
  val degree = adjacent.length

  // Rotates an entry point index.
  def rotCCW(index: Int, times: Int = 1) =
    EntryPoint(tag, (((index + times) % degree) + degree) % degree)

  def dirEdge(index: Int) = DirMultiEdge(EntryPoint(tag, index), adjacent(index))
}


// A directed edge of the multi-planar graph. Each edge has a crossing of the knot.
case class DirMultiEdge(start: EntryPoint, end: EntryPoint) {
  def reverse = DirMultiEdge(end, start)
}

// Each directed edge of MultiGraph has two directed strands, the one going
// left to right (from bottom to top along the directed each), and
// right to left.
// DirStrand represents one of these two directed strands.
// `edge` is the edge of the MultiGraph.
case class DirStrand(edge: DirMultiEdge, isLR: Boolean) {
  def reverse = DirStrand(edge.reverse, isLR)
}

/**
  * Planar graph with parallel edges. Represents black graph of an alternating knot.
  * Each edge represents a negative crossing.
  */
case class MultiGraph(vertices: Map[VertexTag, MultiVertex]) {

  def adjacentEP(ep: EntryPoint): EntryPoint = {
    val startVert = vertices(ep.tag)
    startVert.adjacent(ep.index)
  }

  def dirEdges: Vector[DirMultiEdge] = {
    vertices.values.toVector.flatMap({ v =>
      (0 until v.degree).toVector.map(index => v.dirEdge(index))
    })
  }

  // All directed strands, so each strand is counted twice (with opposite orientations)
  def dirStrands: Vector[DirStrand] =
    dirEdges.flatMap({ edge =>
      Vector(DirStrand(edge, false), DirStrand(edge, true))
    })

  // Rotate edge around starting vertex
  def rotCCW(ep: EntryPoint, times: Int = 1): EntryPoint = {
    val startVertTag = ep.tag
    val startVert = vertices(startVertTag)
    startVert.rotCCW(ep.index, times)
  }

  // Travelling along an oriented strand we get another oriented strand
  def nextOrientedStrand(strand: DirStrand): DirStrand = {
    val ccwRot: Int = if (strand.isLR) 1 else -1
    val endEP: EntryPoint = strand.edge.end

    val startEPNew = rotCCW(endEP, ccwRot)
    val endEPNew = adjacentEP(startEPNew)
    val isLR = !strand.isLR
    DirStrand(DirMultiEdge(startEPNew, endEPNew), isLR)
  }


  // All edges represent negative twists.
  def toPD: Vector[Vector[Int]] = {
    val edges: Vector[DirMultiEdge] = dirEdges
    val orientedStrands: Vector[DirStrand] = orientLink

    def knotStrandIndex(crossing: DirMultiEdge, entrance: Int): Int = {
      if (entrance == 0 || entrance == 1) {
        val isLR = entrance == 0
        1 + orientedStrands.indexWhere({ dirstrand =>
          dirstrand == DirStrand(crossing, isLR) ||
          dirstrand == nextOrientedStrand(DirStrand(crossing.reverse, isLR))
        })
      } else { // entrance is 2 or 3
        knotStrandIndex(crossing.reverse, entrance - 2)
      }
    }

    val pdCode: Vector[Vector[Int]] = 
    edges.flatMap({ e =>
      // Check if bottom left entrance points inwards
      if (!orientedStrands.contains(DirStrand(e, isLR = true))) Vector()
      else {
       Vector((0 until 4).toVector.map(entrance => knotStrandIndex(e, entrance)))
      }
    })
    pdCode
    //pdCode.distinct // edges has each edge with two orientations, so x'ings visited twice
  }

  def toPythonPD: String = {
    val pd = toPD
    def crossingToString(c: Vector[Int]) = c.mkString("[", ",", "]")
    "[" + (pd map (crossingToString) mkString(", ")) + "]"
  }

  def identifyLink = {
    val pd = toPythonPD
    PythonInterface.execute("from spherogram import *")
    PythonInterface.execute("from snappy import *")
    PythonInterface.execute(s"link = Link($pd)")
    PythonInterface.execute("M = link.exterior(); M.simplify()")
    PythonInterface.command("M.identify()")
  }

  // Randomly oriented the components of the link.
  // Returns strands in order, as the link is traversed, one component at a time.
  def orientLink: Vector[DirStrand] = {
    val allStrands: Vector[DirStrand] = dirStrands
    if (allStrands.isEmpty) Vector()
    else {
      def loop(prevStrand: DirStrand, orientedStrands: Vector[DirStrand],
        undetStrands: Vector[DirStrand]): Vector[DirStrand] = {
        val nextStrand = nextOrientedStrand(prevStrand)
        if (orientedStrands.contains(nextStrand) || orientedStrands.contains(nextStrand.reverse)) {
          // We've completed a component
          undetStrands.headOption match {
            case Some(strand) => {
              val undetStrandsNew = undetStrands.filter(s => s != strand && s != strand.reverse)
              loop(strand, orientedStrands :+ strand, undetStrandsNew)
            }
            case None => orientedStrands
          }
        } else {
          val undetStrandsNew = undetStrands.filter(s => s != nextStrand && s != nextStrand.reverse)
          loop(nextStrand, orientedStrands :+ nextStrand, undetStrandsNew)
        }
      }

      val currStrand = allStrands.head
      val undetStrands = allStrands.filter(s => s != currStrand && s != currStrand.reverse)
      loop(currStrand, Vector(currStrand), undetStrands)
    }
  }

  def numPositiveCrossings(orientedStrands: Vector[DirStrand]): Int = {
    // Note all edge of the planar graph represent NEGATIVELY twisted components.
    // Once we orient the link, we can check if a crossing is positive/negative.

    dirEdges.map({ edge =>
      val parallelOriented = orientedStrands.filter(strand => strand.edge == edge).length
      if (parallelOriented == 1) 1 else 0
    }).sum / 2
  }

  // Compute the signature of the link. Orientations on link components are randomly assigned.
  // For a knot the orientation doesn't affect the signature.
  def signature: Int = {
    val orientedStrands: Vector[DirStrand] = orientLink
    (vertices.size-1) - numPositiveCrossings(orientedStrands)
    // Rank of positive definite lattice - num of positive crossings
  }
}

object MultiGraph {
  def fromBlackGraph(bg: BlackGraph, edgeWeights: Vector[(DirEdge, Int)] = Vector()): MultiGraph = {
    val adj: Vector[(Vertex, Vector[Vertex])] = bg.adj.toVector

    def weight(edge: DirEdge): Int = {
      edgeWeights.find({ case (e, _) => e == edge || (e._2, e._1) == edge }) match {
        case Some((_, n)) => n
        case None => 1 // default weight
      }
    }

    def degreeInMG(tag: Vertex) = {
      bg.adj(tag).map(end => weight((tag, end))).sum
    }

    def firstIndex(startTag: Vertex, endTag: Vertex): Int = {
      val image = bg.adj(startTag)

      var i = 0
      var accum = 0
      while (image(i) != endTag) {
        accum += weight((startTag, image(i)))
        i += 1
      }
      accum
    }

    def lastIndex(startTag: Vertex, endTag: Vertex): Int = {
      firstIndex(startTag, endTag) + weight((startTag, endTag)) - 1
    }

    val vertices: Vector[(VertexTag, MultiVertex)] =
    bg.vertices.map({ v =>
      val vAdj: Vector[EntryPoint] = 
      bg.adj(v).flatMap({ vImg =>
        val edge = (v, vImg)
        (0 until weight(edge)).toVector.map(i => EntryPoint(vImg, lastIndex(vImg, v) - i))
      })
      (v, MultiVertex(v, vAdj))
    })

    MultiGraph(vertices.toMap)
  }
}
