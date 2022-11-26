
package ahmad.hfhomology

import spire.implicits._
import spire.math._

object EmbeddingWithDuration {
  type Label = Int
  type Coeffs = Vector[(Int, Label)]
  type Embedding = Vector[Coeffs]
  type Symmetries = Vector[Vector[Label]] // partition of used labels

  def embeddingsMaxDuration(
    numMillis: Long,
    q: IntersectionForm,
    maxRank: Option[Int] = None): Option[Stream[Embedding]] = {
    val initTimeMillis = System.nanoTime() / 1000000L
    val n = q.rank
    // All possible coefficients for basis j
    // Also returns newLabels for each choice of coeffs
    def possCoeffs(partialEmb: Map[Int, Coeffs],
      newLabel: Int = 1,
      j: Int,
      symm: Symmetries
    ): Option[Vector[(Coeffs, Label, Symmetries)]] = {
      val norm = -q(j, j)
      val visited = partialEmb.keys.toVector.sortBy(k => -q(k, k)) // already assigned indices
      /*
      // First work out all possible ways to assign coeffs with
      // already used labels by making sure we pair correctly
      // with previously visited generators
      val impliedCoeffs: Vector[(Coeffs, Symmetries)] =
        visited.foldLeft(Vector[(Coeffs, Symmetries)]((Vector(), symm))) {
          case (vec, i) =>
            vec.flatMap { case (c, cSymm) =>
              extendCoeffs(coeffs = c,
                nbrCoeffs = partialEmb(i),
                k = q(i, j),
                norm + dot(c, c), cSymm)
            }
        }
      //println(s"implied poss: ${impliedCoeffs.length} for norm: $norm")
      //println("partial: " + partialEmb)
      //println(impliedCoeffs.headOption)
       */


      // First work out all possible ways to assign coeffs with
      // already used labels by making sure we pair correctly
      // with previously visited generators
      // `currPoss` is poss coeffs for basis element `j`,
      // together with updated symmetries.
      def computeImpliedCoeffs(
        currPoss: Vector[(Coeffs, Symmetries)] = Vector((Vector(), symm)),
        visitedRemaining: Vector[Int] = visited // visited not yet used to infer info.
      ): Option[Vector[(Coeffs, Symmetries)]] = {
        if (visitedRemaining.isEmpty) Some(currPoss)
        else {
          var emergencyExit = false
          // infer using `i`th vertex
          def computeNewPoss(i: Int) = {
            currPoss.flatMap({ case (c, cSymm) =>
              val res = extendCoeffs(coeffs = c,
                nbrCoeffs = partialEmb(i),
                k = q(i, j), // `j` is the basis vector we're embedding
                norm + dot(c, c), cSymm, initTimeMillis, numMillis)
              res match {
                case Some(extended) => extended
                case None => {
                  emergencyExit = true
                  Vector()
                }
              }
            })
          }
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

          if (emergencyExit || System.nanoTime()/1000000L - initTimeMillis > numMillis) None
          else computeImpliedCoeffs(newPoss, visitedRemaining.filter(i => i != bestInVisited))
        }
      }

      computeImpliedCoeffs() match {
        case Some(impliedCoeffs) => { // Vector[(Coeffs, Symmetries)]
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
          Some(possibleCoeffs)
        }
        case _ => None
      }
    }

    // complete embedding in all possible ways
    def embed(partialEmb: Map[Int, Coeffs],
      newLabel: Int,
      symm: Symmetries
    ): Option[Stream[Embedding]] = {
      if (maxRank.map(newLabel > _ + 1).getOrElse(false)) {
        Some(Stream())
      } else if (partialEmb.size == n) {
        Some(Stream((0 until n).toVector.map(partialEmb(_))))
      } else if (System.nanoTime()/1000000L - initTimeMillis > numMillis) {
        None
      } else if (partialEmb.isEmpty) {
        val j = (0 until n).minBy(i => -q(i, i))
        val res = vectorsOfNorm(-q(j, j)).toStream.flatMap { seq =>
          val coeffs = seq zip (1 to seq.length)
          val newSym: Symmetries = symm ++
            symmetries(seq).map(_.map(i => newLabel + i - 1))
          embed(Map(j -> coeffs), newLabel = seq.length + 1, newSym).getOrElse(Stream())
        }
        if (System.nanoTime()/1000000L - initTimeMillis > numMillis) None else Some(res)
      } else {
        // We want to assign coefficients to the vertex
        // with the least number of possibilities (branch factor)
        val visited = partialEmb.keys.toVector
        val unvisited = (0 until n).filter(i => !visited.contains(i)).toVector

        val unvisited_i = unvisited.minBy({ i =>
          val norm = -q(i,i)
          val pairs = if (visited.exists(j => q(i, j) != 0)) 0 else 1
          (pairs, norm)
        })

        possCoeffs(partialEmb, newLabel, unvisited_i, symm) match {
          case Some(possibleCoeffs) => {
            //println("Selected branch: " + possCoeffsAllNodes(i).length)
            //println("Selected branch: " + possibleCoeffs.length)
            //println(s"partial: $partialEmb")
            //println(possibleCoeffs)
            val res = possibleCoeffs
              .toStream.flatMap({ case (coeffs, nextLabel, cSymm) =>
                embed(partialEmb + (unvisited_i -> coeffs), nextLabel, cSymm)
                  .getOrElse(Stream())
              })
            if (System.nanoTime()/1000000L - initTimeMillis > numMillis) None else Some(res)
          }
          case None => None
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
    symm: Symmetries,
    initTimeMillis: Long,
    numMillis: Long
  ): Option[Vector[(Coeffs, Symmetries)]] = {
    if (norm < 0) Some(Vector())
    else if (System.nanoTime()/1000000L - initTimeMillis > numMillis) None
    else if (nbrCoeffs.isEmpty) {
      if (dot(coeffs, nbrCoeffs) == k) Some(Vector((coeffs, symm))) else Some(Vector())
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
          extendCoeffs(coeffs, nbrCoeffsRest, k + a*b*m, norm, symm, initTimeMillis, numMillis)
        }
        case None => {
          // haven't yet assigned coeffs
          // assign coeffs to all basis elements in nbrCoeffsSymm (none assigned yet)
          var emergencyExit = false
          val numSymm = symmSet.length
          val res = Some(paddedSignedVectorsOfNormAtMost(norm, numSymm).flatMap { seq =>
          //LatticeEmbedding.memoizedSignedVecsWithSymm(norm, numSymm).flatMap { case (seq, seqSymm) =>
            val newCoeffs: Coeffs = coeffs ++ seq.zip(symmSet)
            val newNorm = norm - seq.map(i => i*i).sum
            val newKTarget = k + a*seq.sum

            val newSymm: Symmetries = symmRest ++
            //              seqSymm.map(_.map(i => symmSet(i-1)))
            symmetries(seq).map(_.map(i => symmSet(i-1)))
            extendCoeffs(newCoeffs, nbrCoeffsRest, newKTarget, newNorm, newSymm,
              initTimeMillis, numMillis) match {
              case Some(extended) => extended
              case _ => {
                emergencyExit = true
                Vector()
              }
            }
          })
          if (emergencyExit) None else res
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
    cm.zip(0 until cm.length)
      .groupBy(_._1) // group by cm coeffs
      .values
      .toVector
      .map(partition => partition.map(_._2 + 1)) // only want index+1 (label)
  }

  /**
    *  Sequences of integers with norm at most
    *  norm, where the length of the sequence is exactly m 
    */
  def paddedSignedVectorsOfNormAtMost(norm: Int, m: Int) = {
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
