
package ahmad.hfhomology

import spire.implicits._
import spire.math._

/**
  * Represents the black graph of a knot/link.
  * adj maps a vertex to counter clockwise vector of adjacent vertices
  */
case class BlackGraph(adj: Map[Vertex, Vector[Vertex]]) {
  import BlackGraph._

  val vertices: Vector[Vertex] = adj.keys.toVector.sorted

  // Undirected
  def edges: Vector[DirEdge] = {
    adj.keys.toVector.flatMap({ v =>
      adj(v).filter(_ < v).map(u => (v, u))
    })
  }

  def degree(v: Vertex): Int = adj(v).length

  // Has nuggatory crossing (Reidemeister 1 move)
  def hasNuggatory(edgeWeights: Vector[(DirEdge, Int)]): Boolean = {
    edges.exists { case (u, v) =>
      (degree(u) == 1 || degree(v) == 1) && 
      ! edgeWeights.exists({ case (edge, w) =>
        w > 1 && ((u, v) == edge || (v, u) == edge)
      })
    }
  }

  // Are two symmetries the same symmetry upto an orientation
  // preserving symmetry of the diagram?
  def isConjugateSymmetry(edgeWeights1: Vector[(DirEdge, Int)],
    vertMap1: Map[Vertex, Vertex],
    edgeWeights2: Vector[(DirEdge, Int)],
    vertMap2: Map[Vertex, Vertex]): Boolean = {
    def getWeight(edgeWeights: Vector[(DirEdge, Int)], edge: DirEdge): Int = {
      val u = edge._1
      val v = edge._2
      edgeWeights.find({ case (edge, w) => edge == (u, v) || edge == (v, u) }) match {
        case Some((_, w)) => w
        case None => if (edges.contains((u, v)) || edges.contains((v, u))) 1 else 0
          // Default edge weight is 1
      }
    }

    def vertConj(vMap: Map[Vertex, Vertex]): Boolean = {
      // Does vMap conjugate between vertMap1 qand vertMap2
      // vMap(vertMap1(v)) = vertMap2(vMap(v)) for all v
      vertices.forall { v =>
        vMap(vertMap1(v)) == vertMap2(vMap(v))
      }
    }

    selfIsomorphisms().map(_._2).filter(vertConj).exists({ vMap =>
      // Check that edge weights are preserved
      edges.forall({ case (u, v) =>
        getWeight(edgeWeights1, (u, v)) == getWeight(edgeWeights2, (vMap(u), vMap(v)))
      })
    })
  }

  def numCrossings(edgeWeights: Vector[(DirEdge, Int)]): Int =
    edgeWeights.map(_._2).sum

  def edgeClasses(vertMaps: Vector[Map[Vertex, Vertex]]): Vector[Vector[DirEdge]] = {
    var visited: Vector[DirEdge] = Vector()
    edges.flatMap({ case (u, v) =>
      if (visited.contains((u, v)) || visited.contains((v, u))) Vector()
      else {
        var eqClass: Vector[DirEdge] = Vector((u, v))
        var added = true

        while (added) {
          added = false
          for (vertMap <- vertMaps;
               (v1, v2) <- eqClass) {
            var uImg = vertMap(v1)
            var vImg = vertMap(v2)
            while (!eqClass.contains((uImg, vImg)) && !eqClass.contains((vImg, uImg))) {
              eqClass = eqClass :+ (uImg, vImg)
              added = true
            }
          }
        }
        visited = visited ++ eqClass
        Vector(eqClass)
      }
    })
  }

  // invariant under a subgroup of vertMaps.
  def assignEdgeWeights(vertMaps: Vector[Map[Vertex, Vertex]], maxCrossings: Int = 12
  ): Vector[Vector[(DirEdge, Int)]] = {
    val classes = edgeClasses(vertMaps)

    // i is index of current edge class
    def generate(i: Int,
      edgeWeights: Vector[(DirEdge, Int)],
      remWeight: Int
    ): Vector[Vector[(DirEdge, Int)]] = {
      if (i >= classes.length) {
        if (remWeight >= 0) Vector(edgeWeights) else Vector()
      } else {
        val edgeClass = classes(i)
        val n = edgeClass.length
        (1 to remWeight / n).toVector.flatMap({ w =>
            generate(i+1, edgeWeights ++ edgeClass.map(e => (e, w)), remWeight - n*w)
        })
      }
    }
    //val poss = sequence(classes.toVector.map(ec => (1 to weightLimit).toVector.map((_, ec))))
    //val assignments = poss.map(_.flatMap({ case (w, ec) => ec.map(edge => (edge, w)) }))
    //assignments.filter(ew => numCrossings(ew) <= maxCrossings)
    generate(0, Vector(), maxCrossings)
  }

  """
  def assignEdgeWeights(vertMap: Map[Vertex, Vertex], maxCrossings: Int = 12
  ): Vector[Vector[(DirEdge, Int)]] = {
    val classes = edgeClasses(vertMap)

    // i is index of current edge class
    def generate(i: Int,
      edgeWeights: Vector[(DirEdge, Int)],
      remWeight: Int
    ): Vector[Vector[(DirEdge, Int)]] = {
      if (i >= classes.length) {
        if (remWeight >= 0) Vector(edgeWeights) else Vector()
      } else {
        val edgeClass = classes(i)
        val n = edgeClass.length
        (1 to remWeight / n).toVector.flatMap({ w =>
            generate(i+1, edgeWeights ++ edgeClass.map(e => (e, w)), remWeight - n*w)
        })
      }
    }
    //val poss = sequence(classes.toVector.map(ec => (1 to weightLimit).toVector.map((_, ec))))
    //val assignments = poss.map(_.flatMap({ case (w, ec) => ec.map(edge => (edge, w)) }))
    //assignments.filter(ew => numCrossings(ew) <= maxCrossings)
    generate(0, Vector(), maxCrossings)
  }

  def edgeClasses(vertMap: Map[Vertex, Vertex]): Vector[Vector[DirEdge]] = {
    var visited: Vector[DirEdge] = Vector()
    edges.flatMap({ case (u, v) =>
      if (visited.contains((u, v)) || visited.contains((v, u))) Vector()
      else {
        var eqClass: Vector[DirEdge] = Vector((u, v))
        var uImg = vertMap(u)
        var vImg = vertMap(v)
        while (!eqClass.contains((uImg, vImg)) && !eqClass.contains((vImg, uImg))) {
          eqClass = eqClass :+ (uImg, vImg)
          uImg = vertMap(uImg)
          vImg = vertMap(vImg)
        }
        visited = visited ++ eqClass
        Vector(eqClass)
      }
    })
  }"""

  // Must be a knot
  def transvergentSymmetryInfo(vertMap: Map[Vertex, Vertex],
    edgeWeights: Vector[(DirEdge, Int)]) = {
    assert(det(edgeWeights) % 2 == 1)
    assert(edges.length == edgeWeights.length) // Every edge must have a weight
    val fixedVerts: Vector[Vertex] = vertMap.keySet.filter(k => vertMap(k) == k).toVector
    if (fixedVerts.isEmpty) {
      // periodic
      // Linking number with axis is (up to sign) sum (weights of fixed edges)
      // Fixed edges have endpoints interchanged.

      val linking = edgeWeights.filter({ case (edge, w) =>
        vertMap(edge._1) == edge._2 && vertMap(edge._2) == edge._1
      }).map(_._2).sum
      ("Periodic", linking)
    } else {
      // if fixed edges form a loop then periodic
      // forming a loop is same as #(fixed edges) = #(fixed verts).
      val fixedEdges = edgeWeights.filter({ case (edge, w) =>
        vertMap(edge._1) == edge._1 && vertMap(edge._2) == edge._2 && w % 2 == 1 // edge weight odd to contribute to loop
      })

      if (fixedEdges.length == fixedVerts.length) { // Periodic case
         // linking number (upto sign) is #('fixed' edges)
        ("Periodic", fixedEdges.length)
      } else {
        ("Strongly invertible", 0)
      }
    }
  }

  // Returns (type of iso, Map[Vertex, Vertex])
  def selfIsomorphisms(includeReflection: Boolean = true
  ): Vector[(SymmetryType, Map[Vertex, Vertex])] = {
    val orientPrev = isomorphismsTo(this)
    val orientRev = if (includeReflection) isomorphismsTo(this.mirror) else Vector()
    orientPrev.map(sym => (Intravergent(order(sym)), sym)) ++
      orientRev.map(sym => (Transvergent(order(sym)), sym))
  }

  def det(edgeWeights: Vector[(DirEdge, Int)] = Vector()) = {
    val mat = toLaplaceMatrix(edgeWeights)
    mat.slice(1, 1, mat.nRows, mat.nCols).absDet
  }

  def isKnot(edgeWeights: Vector[(DirEdge, Int)]) = {
    det(edgeWeights) % 2 == 1
  }


  // Each edge represents a negative crossing
  def signature(edgeWeights: Vector[(DirEdge, Int)] = Vector()): Int = {
    MultiGraph.fromBlackGraph(this, edgeWeights).signature
  }


  // Is the lattice embedding invariant
  // Image of vertices are rows of `emb`.
  def isEmbeddingInvariant(emb: Matrix, vertMap: Map[Vertex, Vertex]): Boolean = {
    val matTransformed = Matrix(
      (0 until emb.nRows).toVector.map({ i =>
        val vImg = vertMap(vertices(i))
        val iImg = vertices.indexOf(vImg)
        emb.mat(iImg)
      }))
    LatticeEmbedding.equivEmbeddings(emb, matTransformed)
  }

  // If the lattice embedding is invariant, then computes all the possible g-signatures
  // of the closed 4-manifold.
  def invarEmbGSig(emb: Matrix, vertMap: Map[Vertex, Vertex]) = {
    val matTransformed = Matrix(
      (0 until emb.nRows).toVector.map({ i =>
        val vImg = vertMap(vertices(i))
        val iImg = vertices.indexOf(vImg)
        emb.mat(iImg)
      }))
    //println(emb)
    LatticeEmbedding.gSignatures(emb.dropLastRows(1), matTransformed.dropLastRows(1))
  }

  // Image vectors are rows
  def embeddings(edgeWeights: Vector[(DirEdge, Int)] = Vector(), codim: Int = 0): Stream[Matrix] = {
    val mat = toLaplaceMatrix(edgeWeights)
    // Delete first row and column to get intersection form
    val q = IntersectionForm.fromMatrix(mat.slice(1, 1, mat.nRows, mat.nCols))
    val embs = q.embeddingsAsMatrices(Some(q.rank + codim))
    // Add back a first row for the vertex deleted
    // Added so that the sum of the rows is 0.
    embs.map({ mat =>
      val negRowSums = (0 until mat.nCols).toVector.map(i => mat.mat.map(row => -row(i)).qsum)
      Matrix(negRowSums +: mat.mat)
    })
  }

  def invEmbeddings(vertMap: Map[Vertex, Vertex],
    edgeWeights: Vector[(DirEdge, Int)] = Vector(),
    codim: Int = 0) = {
    val embs = embeddings(edgeWeights, codim)
    embs.filter({ mat =>
      val matTransformed = Matrix(
      (0 until mat.nRows).toVector.map({ i =>
        val vImg = vertMap(vertices(i))
        val iImg = vertices.indexOf(vImg)
        mat.mat(iImg)
      }))
      LatticeEmbedding.equivEmbeddings(mat, matTransformed)
    })
  }

  def mirror = BlackGraph(adj.map({ case (v, vec) => (v, vec.reverse)}))

  // All edge weights are 1
  def toLaplaceMatrix: Matrix = toLaplaceMatrix(Vector())

  // Vertices are ordered according to this.vertices
  // This is like the goeritz form before a row/column have been deleted
  def toLaplaceMatrix(edgeWeights: Vector[(DirEdge, Int)]): Matrix = {
    val n = vertices.length

    def getWeight(edge: DirEdge): Int = {
      val u = edge._1
      val v = edge._2
      edgeWeights.find({ case (edge, w) => edge == (u, v) || edge == (v, u) }) match {
        case Some((_, w)) => w
        case None => if (edges.contains((u, v)) || edges.contains((v, u))) 1 else 0
          // Default edge weight is 1
      }
    }

    val mat = 
      (0 until n).toVector.map({ i =>
        (0 until n).toVector.map({ j =>
          if (i != j) getWeight(vertices(i), vertices(j))  
          else { // i == j
            val u = vertices(i)
            -adj(u).map(v => getWeight((u, v))).sum
          }
        })
      })
    Matrix(mat)
  }

  def isomorphismsTo(pg: BlackGraph): Vector[Map[Vertex, Vertex]] = {
    // Is mapping vertices of lst to lst2 (in order) compatible with currMap (partial map)
    def compatible(currMap: Map[Vertex, Vertex], lst: Vector[Vertex], lst2: Vector[Vertex]) = {
      if (lst.length != lst2.length) false
      else {
        (0 until lst.length).forall { i => 
          if (currMap.contains(lst(i))) currMap(lst(i)) == lst2(i)
          else true
        }
      }
    }

    def rotRight[A](vec: Vector[A], n: Int) = {
      val m = vec.length
      vec.slice(m-n, m) ++ vec.slice(0, m-n)
    }

    def completeIso(currMap: Map[Vertex, Vertex], unvisited: Vector[Vertex],
      visited: Vector[Vertex]): Vector[Map[Vertex, Vertex]] = {
      //println(s"Entered: $currMap, $unvisited, $visited")
      // unvisited are vertices of this graph which have been assigned but haven't been visited yet
      unvisited.headOption match {
        case None => Vector(currMap)
        case Some(v) => {
          // enumerate possible vertex rotations with its image adjacency compatible with currMap
          (0 until adj(v).length).toVector
            .map(i => rotRight(adj(v), i))
            .filter(compatible(currMap, _, pg.adj(currMap(v))))
            .flatMap { adjToV =>
              val visitedNew = visited :+ v
              val unvisitedNew = unvisited.tail ++
                adjToV.filter(u => !visited.contains(u) && !unvisited.contains(u))
              //println(s"old unvisited: $unvisited, new unvisited: $unvisitedNew, new visited: $visitedNew")
              val currMapNew = currMap ++
                ((0 until adjToV.length).toVector
                  .map(i => (adjToV(i), pg.adj(currMap(v))(i))))
              completeIso(currMapNew, unvisitedNew, visitedNew)
            }
        }
      }
    }

    vertices.headOption match {
      case None => if (pg.vertices.isEmpty) Vector(Vector[(Vertex, Vertex)]().toMap) else Vector()
      case Some(v) => {
        pg.vertices.flatMap(vImg =>
          completeIso(Map((v, vImg)), Vector(v), Vector())
        )
      }
    }
  }

  def toMultiGraph(edgeWeights: Vector[(DirEdge, Int)] = Vector()) =
    MultiGraph.fromBlackGraph(this, edgeWeights)

  def identifyLink(edgeWeights: Vector[(DirEdge, Int)] = Vector()) =
    toMultiGraph(edgeWeights).identifyLink
}

object BlackGraph {

  /*
   * Intravergent means rotation in plane (axis perp to plane), 
   * transvergent is rotation with axis on plane.
   * 
   */
  trait SymmetryType
  case class Intravergent(order: Int) extends SymmetryType {
    override def toString = {
      s"intravergent, order $order"
    }
  }

  case class Transvergent(order: Int) extends SymmetryType {
    override def toString = {
      s"transvergent, order $order"
    }
  }

/*
  case class SymmetryType(intravergent: Boolean, order: Int) {
    override def toString = {
      val vergence = if (intravergent) "Intravergent" else "Transvergent"
      s"$vergence, order $order"
    }
  }
 */

  // x -> map2(map1(x))
  def compose(vertMap1: Map[Vertex, Vertex], vertMap2: Map[Vertex, Vertex]) = {
    vertMap1.mapValues(x => vertMap2(x))
  }

  // vertMap^n = id, returns n
  def order(vertMap: Map[Vertex, Vertex]): Int = {
    def isIdentity(map: Map[Vertex, Vertex]): Boolean = map.forall({ case (x, y) => x == y })

    var n = 1
    var currMap = vertMap
    while (!isIdentity(currMap)) {
      n += 1
      currMap = compose(currMap, vertMap)
    }
    n
  }

  def fromPlantriFile(filename: String): Iterator[BlackGraph] = {
    import scala.io.Source

    Source.fromFile(filename).getLines().map(line => fromPlantri(line))
  }

  // A single planar graph description from Plantri. For example:
  // 5 bcde,aedc,abd,acbe,adb
  // 5 here means 5 vertices
  // In plantri you can generate output like this: ./plantri -a -m1 -c1 -p 2 out.txt
  def fromPlantri(line: String): BlackGraph = {
    // Ignore first number
    val adjStrings: Array[String] = line.split(" ")(1).split(",")
    val alpha = 'a' to 'z'
    BlackGraph((0 until adjStrings.length).toVector
      .map(i => (alpha(i).toString, adjStrings(i).split("").toVector)).toMap
      )
  }

}
