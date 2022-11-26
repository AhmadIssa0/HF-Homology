
package ahmad.hfhomology

import spire.implicits._
import spire.math._

object LatticeEmbedding {
  type Label = Int
  type Coeffs = Vector[(Int, Label)]
  type Embedding = Vector[Coeffs]
  type Symmetries = Vector[Vector[Label]] // partition of used labels

  /**
    *  Returns embedding as matrix (so image of vectors are ROWS).
    *  This is the transpose of the inclusion map on homology.
    */
  def embeddingToMatrix(emb: Embedding): Matrix = {
    val coeffLabels = emb.flatMap(_.map(_._2)).distinct
    val mat =
      for (i <- (0 until emb.length).toVector) yield {
        val coeffs = emb(i)
        for (j <- (0 until coeffLabels.length).toVector) yield {
          coeffs.find(_._2 == coeffLabels(j)) match {
            case Some((w, _)) => SafeLong(w)
            case None => SafeLong(0)
          }
        }
      }
    Matrix(mat)
  }

  def codimOfEmb(emb: Embedding): Int = {
    val mat = embeddingToMatrix(emb)
    mat.nCols - mat.nRows
  }

  /*  Are two lattice embeddings, given as matrices with image of elements given as
   *  rows equivalent upto a change of basis.
   */
  def equivEmbeddings(emb1: Matrix, emb2: Matrix, debug: Boolean = false): Boolean = {
    assert(emb1.dimensions == emb2.dimensions)

    val e1 = emb1.transpose
    val e2 = emb2.transpose

    val n = e1.nRows
      (0 until n).forall { i =>
        val c1 = e2.mat.count(row => row == e1(i) || row == e1(i).map(-_))
        val c2 = e1.mat.count(row => row == e1(i) || row == e1(i).map(-_))
        if (debug && c1 != c2)
          println(s"Column $i of emb1 appears $c2 times in emb1 but $c1 times in emb2")
        c1 == c2
    }
  }

  // Returns automorphism of (Z^n, Id) which maps emb1 to emb2
  // Vector(Vector(2, 1, 3, -5, -4, 6)) means there is one isomorphism
  // It sends e_1 to e_2, e_2 to e_1, e_3 to e_3, e_4 to -e_5, e_5 to -e_4 and e_6 to e_6.
  def embeddingEquivs(emb1: Matrix, emb2: Matrix): Vector[Vector[Int]] = {
    assert(emb1.dimensions == emb2.dimensions)
    val e1 = emb1.transpose
    val e2 = emb2.transpose

    val n = e1.nRows
    type Mat = Vector[Vector[Int]]
    // i is index of row of e1 we're matching with a row of e2.
    def enumerate(i: Int, currEquiv: Vector[Int]): Vector[Vector[Int]] = {
      if (i >= n) Vector(currEquiv)
      else {
        val indices = (0 until n)
          .filter(j => !currEquiv.contains(j+1) && !currEquiv.contains(-j-1))

        val pos = indices.filter(j => e2(j) == e1(i)).map(j => currEquiv :+ (j+1)).toVector
        val neg = indices.filter(j => e2(j) == e1(i).map(-_)).map(j => currEquiv :+ (-j-1)).toVector
        pos.flatMap(partialEquiv => enumerate(i+1, partialEquiv)) ++
        neg.flatMap(partialEquiv => enumerate(i+1, partialEquiv))
      }
    }
    enumerate(0, Vector())
  }

  // Giving two lattice embeddings, computes automorphisms of Z^n getting
  // from emb1 to emb2 and then computes the g-signature of these automorphisms
  // This requires the automorphisms to have order 2.
  def gSignatures(emb1: Matrix, emb2: Matrix) = {
    embeddingEquivs(emb1, emb2).map(iso =>
      (0 until iso.length).map({ i =>
        if (i+1 == iso(i)) 1
        else if (i+1 == -iso(i)) -1
        else 0
      }).sum
    ).distinct
  }




  def embeddings(q: IntersectionForm, maxRank: Option[Int] = None) = {
    val n = q.rank
    // All possible coefficients for basis j
    // Also returns newLabels for each choice of coeffs
    def possCoeffs(partialEmb: Map[Int, Coeffs],
      newLabel: Int = 1,
      j: Int,
      symm: Symmetries
    ): Vector[(Coeffs, Label, Symmetries)] = {
      val norm = -q(j, j)
      val visited = partialEmb.keys.toVector//.sortBy(k => -q(k, k)) // already assigned indices
      
      // First work out all possible ways to assign coeffs with
      // already used labels by making sure we pair correctly
      // with previously visited generators
      // `currPoss` is poss coeffs for basis element `j`,
      // together with updated symmetries.
      def computeImpliedCoeffs(
        currPoss: Vector[(Coeffs, Symmetries)] = Vector((Vector(), symm)),
        visitedRemaining: Vector[Int] = visited // visited not yet used to infer info.
      ): Vector[(Coeffs, Symmetries)] = {
        if (visitedRemaining.isEmpty) currPoss
        else {
          // infer using `i`th vertex
          def computeNewPoss(i: Int) = {
            currPoss.flatMap({ case (c, cSymm) =>
                    extendCoeffs(coeffs = c,
                      nbrCoeffs = partialEmb(i),
                      k = q(i, j), // `j` is the basis vector we're embedding
                      norm + dot(c, c), cSymm)
            })
          }

          // Resulting in fewest possibilities
          // Infer pairing with sequences of norm 2's first, in linear order.
          /*
          val (newPoss, bestInVisited) =
            if (visitedRemaining.exists(i => -q(i,i) <= 2)) {
              val smallestNorm = visitedRemaining.map(i => -q(i,i)).min
              val i = 
              if (smallestNorm == 1) {
                visitedRemaining.minBy(j => -q(j,j))
              } else {
                val visitedInferred = visited.filter(j => !visitedRemaining.contains(j))
                val visitedRemNorm2 = visitedRemaining.filter(i => -q(i,i) == 2)
                visitedRemNorm2.find(m => visitedInferred.exists(k =>
                                                             q(k, m) != 0))
                  .getOrElse(visitedRemNorm2(0))
              }

              (computeNewPoss(i), i)
            } else {              
              visitedRemaining
                .map({i =>
                  // number of possibilities if we use `i`th basis element to infer.
                  (computeNewPoss(i), i)
                }).minBy(_._1.length)
           }*/
          
          val visitedInferred = visited.filter(j => !visitedRemaining.contains(j))
          val bestInVisited = visitedRemaining.minBy({ i =>
            val norm = -q(i,i)
            val pairs =
              if (visitedInferred.exists(j => q(j, i) != 0)) 0 else 1
              /*else if (visited.exists(j => q(j, i) != 0)) 1
              else 2*/
            (pairs, norm)
            //(norm, pairs)
            })
          val newPoss = computeNewPoss(bestInVisited)
           
          computeImpliedCoeffs(newPoss, visitedRemaining.filter(i => i != bestInVisited))
        }
      }

      val impliedCoeffs: Vector[(Coeffs, Symmetries)] = computeImpliedCoeffs()
      //println(s"implied poss: ${impliedCoeffs.length} for norm: $norm")
      //println("partial: " + partialEmb)
      //println(impliedCoeffs.headOption)

      //println(s"implied: for j=$j (w=$norm) is ")
      //impliedCoeffs.foreach { println }
      // Extend implied coeffs to coefficients of new basis elements
      // so that the image has the correct self-pairing, then
      // recursively work out remaining coeffs
      val possibleCoeffs: Vector[(Coeffs, Label, Symmetries)] = 
      impliedCoeffs.flatMap { case (coeffs, cSymm) =>
        vectorsOfNorm(norm + dot(coeffs, coeffs),
          maxRank.map(_  - coeffs.length)
        ).map { v =>
          val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
            .filter(_._1 != 0) // don't want to include 0 coefficients
          val newSym: Symmetries = cSymm ++ symmetries(v).map(_.map(i => newLabel + i - 1))
          (fullCoeffs, newLabel + v.length, newSym)
        }
      }
      //println("branch: " + possibleCoeffs.length)
      possibleCoeffs
    }

    // complete embedding in all possible ways
    def embed(partialEmb: Map[Int, Coeffs],
      newLabel: Int,
      symm: Symmetries
    ): Stream[Embedding] = {
      if (maxRank.map(newLabel > _ + 1).getOrElse(false)) {
        Stream()
      } else if (partialEmb.size == n) {
        Stream((0 until n).toVector.map(partialEmb(_)))
      } else if (partialEmb.isEmpty) {
        val j = (0 until n).minBy(i => -q(i, i))
        vectorsOfNorm(-q(j, j)).toStream.flatMap { seq =>
          val coeffs = seq zip (1 to seq.length)
          val newSym: Symmetries = symm ++ symmetries(seq).map(_.map(i => newLabel + i - 1))
          embed(Map(j -> coeffs), newLabel = seq.length + 1, newSym)
        }
      } else {
        // We want to assign coefficients to the vertex
        // with the least number of possibilities (branch factor)
        val visited = partialEmb.keys.toVector
        val unvisited = (0 until n).filter(i => !visited.contains(i)).toVector

        /*
        // (element of unvisited, and possible coeffs arising from picking it)
        // we deal with strings of two's separately. otherwise, we minimise
        // the branch factor.
        val (i, possibleCoeffs) = if (unvisited.map(j => -q(j,j)).min <= 2) {
          val smallestNorm = unvisited.map(j => -q(j,j)).min
          //println(s"smallestNorm: $smallestNorm")
          val i = 
          if (smallestNorm == 1) {
            unvisited.zipWithIndex.minBy(j => -q(j._1,j._1))._2
          } else {
            unvisited.zipWithIndex.find({j =>
                        -q(j._1,j._1) == 2 && visited.exists(k => q(k, j._1) != 0)})
                     .map(_._2)
                     .getOrElse(unvisited.indexWhere(j => -q(j,j) == 2))
          }

          (i, possCoeffs(partialEmb, newLabel, unvisited(i), symm))
        } else {
          // compute branch with minimal branch factor
          // possible coefficients for each unvisited
          val possCoeffsAllNodes: Vector[Vector[(Coeffs, Label, Symmetries)]] =
            for (i <- unvisited)
            yield possCoeffs(partialEmb, newLabel, i, symm)
          // index of possCoeffsAllNodes with minimum branch factor
          val i = possCoeffsAllNodes.map(_.length).zipWithIndex.min._2
          (i, possCoeffsAllNodes(i))
         }*/
        val unvisited_i = unvisited.minBy({ i =>
          val norm = -q(i,i)
          val pairs = if (visited.exists(j => q(i, j) != 0)) 0 else 1
          (pairs, norm)
        })
        val possibleCoeffs = possCoeffs(partialEmb, newLabel, unvisited_i, symm)
        //println("Selected branch: " + possCoeffsAllNodes(i).length)
        //println(s"unvisited norms: ${unvisited.map(i => -q(i,i))}")
        //println(s"Selected branch: ${possibleCoeffs.length} norm: ${-q(unvisited(i),unvisited(i))}")
        //println(s"partial: $partialEmb")
        //println(possibleCoeffs)
        possibleCoeffs
          .toStream.flatMap { case (coeffs, nextLabel, cSymm) =>
          embed(partialEmb + (unvisited_i -> coeffs), nextLabel, cSymm)
        }
      }
    }
    embed(Map(), 1, Vector())
  }
   /**
    * Sequences of non-increasing positive integers with norm given
    * by norm.
    */
  def vectorsOfNorm(norm: Int): Vector[Vector[Int]] = {
      def loop(
        rem: Int = norm,
        maxInRest: Int = norm
      ): Vector[Vector[Int]] = {
        if (rem == 0) Vector(Vector())
        else {
          val n = min(maxInRest, sqrt(rem.toDouble).toInt)
          for (
            i <- (1 to n).toVector;
            lst <- loop(rem - i * i, i)
          ) yield (i +: lst)
        }
      }
    loop()
  }

  /**
    *  Sequences of non-increasing positive integers with norm given by
    *  norm, where the length of the sequence is at most m.
    */
  def vectorsOfNorm(norm: Int, m: Int): Vector[Vector[Int]] = {
    def loop(
        rem: Int = norm,
        maxInRest: Int = norm,
        lenOfRest: Int = m
      ): Vector[Vector[Int]] = {
      if (rem == 0 && lenOfRest >= 0) Vector(Vector())
      else if (lenOfRest < 0 || (lenOfRest == 0 && rem > 0)) Vector()
      else {
        val n = min(maxInRest, sqrt(rem.toDouble).toInt)
        for (
          i <- (1 to n).toVector;
          lst <- loop(rem - i * i, i, lenOfRest - 1)
        ) yield (i +: lst)
      }
    }
    loop()
  }

  def vectorsOfNorm(norm: Int, m: Option[Int]): Vector[Vector[Int]] = m match {
    case Some(maxRank) => vectorsOfNorm(norm, maxRank)
    case None => vectorsOfNorm(norm)
  }

  /**
   * When we know some of the coefficients of an embedding
   * of a node and we want work out more coefficients using
   * the condition that Q(node, some other node) = k and
   * Q(node, node) <= norm. 
   * We also know some basis vectors can be permuted, so up to symmetry
   * we can pick assign coeffs of vectors which can be permuted 
   * in decreasing order.
   * @param coeffs Coefficients which we only partially know.
   * @param nbrCoeffs Want Q(coeffs, nbrCoeffs) = k.
   */
  def extendCoeffs(
    coeffs: Coeffs,
    nbrCoeffs: Coeffs,
    k: Int,
    norm: Int,
    symm: Symmetries
  ): Vector[(Coeffs, Symmetries)] = {
    if (norm < 0) Vector()
    else if (nbrCoeffs.isEmpty) {
      if (dot(coeffs, nbrCoeffs) == k) Vector((coeffs, symm)) else Vector()
    } else {
      val (a, e_n) = nbrCoeffs(0) // e_n is label of basis elt we're working with
      val (symmSets, symmRest) = symm.partition(p => p.contains(e_n))
      val symmSet = symmSets(0) // only one element in symmSets
      val (nbrCoeffsSymm, nbrCoeffsRest) = nbrCoeffs.partition(c => symmSet contains c._2)
      // by symmetry assumption all coeffs of basis elts in nbrCoeffsCurr should be equal

      coeffs.find(_._2 == e_n) match {
        case Some((b, _)) => {
          // already assigned a coefficient of b to e_n (and hence all symm to e_n)
          val m = nbrCoeffsSymm.length // size of symmetry class
          extendCoeffs(coeffs, nbrCoeffsRest, k + a*b*m, norm, symm)
        }
        case None => {
          // haven't yet assigned coeffs
          // assign coeffs to all basis elements in nbrCoeffsSymm (none assigned yet)
          val numSymm = symmSet.length
          
          paddedSignedVectorsOfNormAtMost(norm, numSymm).flatMap { seq =>
          //memoizedSignedVecsWithSymm(norm, numSymm).flatMap { case (seq, seqSymm) =>
            val newCoeffs: Coeffs = coeffs ++ seq.zip(symmSet)
            val newNorm = norm - seq.map(i => i*i).sum
            val newKTarget = k + a*seq.sum

            val newSymm: Symmetries = symmRest ++
                          //seqSymm.map(_.map(i => symmSet(i-1)))
                        symmetries(seq).map(_.map(i => symmSet(i-1)))
            extendCoeffs(newCoeffs, nbrCoeffsRest, newKTarget, newNorm, newSymm)
          }
        }
      }
    }
  }

  def dot(c: Coeffs, c2: Coeffs): Int = {
    if (c.isEmpty || c2.isEmpty) 0
      else {
        val m = max(c2.map(_._2).max, c.map(_._2).max) + 1
        val arr: Array[Int] = Array.fill[Int](m)(0)
        val arr2 = Array.fill[Int](m)(0)
        c.foreach { case (n, i) => arr(i) = n }
        c2.foreach { case (n, i) => arr2(i) = n }
        (0 until arr.length).map(i => -arr(i)*arr2(i)).sum
      }
  }

  // Given Vector(1,1,1,2,2,3) turns it into
  // Vector(Vector(1,2,3), Vector(4, 5), Vector(6)) (indices+1 of equal elements)
  def symmetries(cm: Vector[Int]): Symmetries = {
    /*
    cm.zip(0 until cm.length)
      .groupBy(_._1) // group by cm coeffs
      .values
      .toVector
      .map(partition => partition.map(_._2 + 1)) // only want index+1 (label)
     */
    // We assume that cm is ordered so that equal elements are contiguous
    var i = cm.length - 2
    var prev = cm.length - 1
    var res: List[Vector[Int]] = List()
    while (i >= 0) {
      if (cm(i) != cm(i+1)) {
        res = (i+2 to prev+1).toVector :: res
        prev = i
      }
      i -= 1
    }
    res = (1 to prev+1).toVector :: res
    res.toVector
  }

  // Taken from: https://stackoverflow.com/questions/16257378/is-there-a-generic-way-to-memoize-in-scala
  def memoize[I, O](f: I => O): I => O = new scala.collection.mutable.HashMap[I, O]()
  { self =>
    override def apply(key: I) = self.synchronized(getOrElseUpdate(key, f(key)))
  }

  /**
    * Returns output of both A = `paddedSignedVectorsOfNormAtMost` and
    * `symmetries` fn applied to all elements of A.
    * We cache this function as it's called many times in `extendCoeffs`.
    */
  def signedVecsWithSymm(norm: Int, m: Int
  ): Vector[(Vector[Int], Vector[Vector[Int]])] = {
    paddedSignedVectorsOfNormAtMost(norm, m).map({ seq => (seq, symmetries(seq)) })
  }

  val memoizedSignedVecsWithSymm = memoize[Tuple2[Int, Int], Vector[(Vector[Int], Vector[Vector[Int]])]]({ case (n, m) => signedVecsWithSymm(n, m) })

  /**
    *  Sequences of integers with norm at most
    *  norm, where the length of the sequence is exactly m 
    */
  def paddedSignedVectorsOfNormAtMost(norm: Int, m: Int): Vector[Vector[Int]] = {
    // for repeated entry in seq, eg 3, 3, 3 once we have a minus,
    // every next entry must have a minus
    def allPossibleSigns(seq: Vector[Int], prev: Option[Int]): Vector[Vector[Int]] =
      if (seq.isEmpty) Vector(Vector())
      else {
        val (a, rest) = (seq.head, seq.tail)
        prev match {
          case Some(b) if b == -a => allPossibleSigns(rest, Some(-a)).map((-a) +: _)
          case _ =>
            allPossibleSigns(rest, Some(a)).map(a +: _) ++
            allPossibleSigns(rest, Some(-a)).map((-a) +: _)
        }
      }

    vectorsOfNormAtMost(norm, m).flatMap(seq => allPossibleSigns(seq, None))
      .map(seq =>
      seq ++ Vector.fill(m - seq.length)(0)
      )
  }

    /**
    *  Sequences of non-increasing positive integers with norm at most
    *  norm, where the length of the sequence is at most m.
    */
  def vectorsOfNormAtMost(norm: Int, m: Int): Vector[Vector[Int]] = {
    def loop(
        rem: Int = norm, // remaining left of norm
        maxInRest: Int = norm,
        lenOfRest: Int = m
      ): Vector[Vector[Int]] = {
      if (rem >= 0 && lenOfRest == 0) Vector(Vector())
      else if (lenOfRest <= 0) Vector()
      else {
        val n = min(maxInRest, sqrt(rem.toDouble).toInt)
        val res = for (
          i <- (1 to n).toVector;
          lst <- loop(rem - i * i, i, lenOfRest - 1)
        ) yield (i +: lst)
        res :+ Vector()
      }
    }
    loop()
  }
}
