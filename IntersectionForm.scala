
package ahmad.hfhomology

import spire.implicits._
import spire.math._

case class IntersectionForm(q: Vector[Vector[Int]]) {
  import IntersectionForm._
  lazy val rank = q.length

  def directSum(that: IntersectionForm): IntersectionForm = {
    val n = this.rank + that.rank
    val mat = 
    for (i <- 0 until n toVector) yield {
      for (j <- 0 until n toVector) yield {
        if (i < this.rank && j < this.rank) q(i)(j)
        else if (i >= this.rank && j >= this.rank) that.q(i - rank)(j - rank)
        else 0
      }
    }
    IntersectionForm(mat)
  }

  def addGenerator(row: Vector[Int]): IntersectionForm = {
    require(row.length == rank + 1, "Wrong dimensions.")
    val q =
      for (i <- (0 until rank + 1).toVector) yield {
        for (j <- (0 until rank + 1).toVector) yield {
          (i, j) match {
            case (x, y) if x < rank && y < rank => this.q(x)(y)
            case (x, y) => row(min(x, y))
          }
        }
      }
    IntersectionForm(q)
  }

  def charSublinks: Vector[Vector[SafeLong]] = Spin.charSublinks(Matrix(q))

  def muBar: Vector[SafeLong] = {
    // Assumes that intersection form is NEGATIVE definite.
    val Q = Matrix(q)

    for (v <- charSublinks) yield {
      rank + (Matrix(Vector(v)) * Q * Matrix(Vector(v)).transpose)(0)(0)
    }
  }

  def deleteGenerator(i: Int): IntersectionForm = {
    assert(i >= 0 && i < rank, "$i not in range of intersection form.")
    IntersectionForm(toMatrix.minor(i, i).toIntVector)
  }


  /**  Returns pairs of embeddings (A_1^T, A_2^T) such that
    *    im (A_1^T | A_2^T) = Z^m, where m = number of rows.
    *  This is equivalent to im(A_1^T)/im(Q) (+) im(A_2^T)/im(Q) = coker(Q),
    *   where Q = A_1^T A_1.
    *  This is a necessary condition to embed in S^4.
    */
  def complementaryEmbeddings = {
    val embs = embeddingsAsMatrices(Some(rank)).toVector
    val combs = for (emb1 <- embs; emb2 <- embs) yield { (emb1, emb2) }

    combs.filter({ case (emb1, emb2) =>
      emb1.adjoin(emb2).isSurjective
    }).toStream
  }

  def hasComplementaryEmbeddings = {
    val embs = embeddingsAsMatrices(Some(rank))
    val combs = for (emb1 <- embs; emb2 <- embs) yield { (emb1, emb2) }

    combs.exists({ case (emb1, emb2) =>
      emb1.adjoin(emb2).isSurjective
    })
  }

  def embImageHomology = {
    val q = this
    val qx = q.toMatrix
    val (diag, left, right) = qx.extendedSmithForm

    //q.embeddings(6).foreach { println _ }
    q.embeddingsAsMatrices(Some(q.rank)).map { a =>
      val b = left*a*right
      //println(diag)
      Matrix.fromFunction(diag.nRows, diag.nCols, { case (i, j) =>
        b(i)(j) % diag(i)(i)
      })
    }
  }

  /**
    *  Returns embeddings as matrices (so image of vectors are ROWS).
    *  This is the transpose of the inclusion map on homology.
    */
  def embeddingsAsMatrices(maxRank: Option[Int] = None): Stream[Matrix] = {
    embeddings(maxRank).map { emb =>
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
  }

  def apply(i: Int, j: Int): Int = q(i)(j)

  def embeddings(): Stream[Embedding] = embeddings(maxRank = None)

  def embeddings(maxRank: Int): Stream[Embedding] = embeddings(Some(maxRank))

  // Enumerate embeddings for maximum of `numMillis` milliseconds.
  def embeddingsMaxDuration(
    numMillis: Long,
    maxRank: Option[Int] = None
  ): Option[Stream[Embedding]] =
    IntersectionForm.embeddingsMaxDuration(numMillis, this, maxRank)

  def embeddings(maxRank: Option[Int] = None): Stream[Embedding] =
    IntersectionForm.embeddings(this, maxRank)

  def codim0Embeddings: Stream[Embedding] = IntersectionForm.embeddings(this, Some(rank))

  def changemakerEmbeddings = IntersectionForm.changemakerEmbeddings(this)
  def halfIntCMEmbeddings = IntersectionForm.halfIntCMEmbeddings(this)

  def pair(v1: Vector[Int], v2: Vector[Int]): Int = {
    require (v1.length == rank && v2.length == rank)

    def dot(w1: Vector[Int], w2: Vector[Int]): Int =
      (0 until w1.length).map(i => w1(i) * w2(i)).sum

    val colVec = q.map(row => dot(row, v2))
    dot(v1, colVec)
  }

  def toMathematica: String =
    "{" + q.map(v => "{" + v.mkString(",") + "}").mkString(",") + "}"

  override def toString = toMathematica

  def toMatrix: Matrix =
    Matrix(q.map(_.map(SafeLong(_))))

  def det = toMatrix.absDet
  /** Apply Laufer's algorithm.
    * Assumes that the intersection form comes
    * from a negative definite plumbing tree
    */
  def isLSpace: Boolean = {
    def basisVector(i: Int) = (0 until rank).toVector.map { j =>
      if (j == i) 1 else 0
    }

    def add(v: Vector[Int], w: Vector[Int]) =
      (0 until v.length).toVector.map(i => v(i) + w(i))

    val basisVectors = (0 until rank).map(basisVector)

    def lauferIsLSpace(K: Vector[Int]): Boolean = {
      val pairings = basisVectors.map(b => pair(b, K))
      if (pairings.exists(_ >= 2)) false
      else if (pairings.exists(_ == 1)) {
        val i = pairings.indexOf(1)
        lauferIsLSpace(add(K, basisVectors(i)))
      } else true
    }

    var K0 = Vector.fill(rank)(1)
    lauferIsLSpace(K0)
  }

}

object IntersectionForm {
  type Label = Int
  type Coeffs = Vector[(Int, Label)]
  type Embedding = Vector[Coeffs]
  type Symmetries = Vector[Vector[Label]] // partition of used labels


  def fromMatrix(mat: Matrix): IntersectionForm = {
    IntersectionForm(mat.mat.map(row => row.map(safelong => safelong.toInt)))
  }

  /* Finds all integer changemaker embeddings assuming that
   * the given lattice has no vectors of norm -1.
   */
  def changemakerEmbeddings(q0: IntersectionForm): Vector[Embedding] = {
    val homology = q0.det.toInt
    val q = q0.directSum(IntersectionForm(Vector(Vector(-homology))))
    val maxRank = q.rank
    val n = maxRank
    // All possible coefficients for basis j
    // Also returns newLabels for each choice of coeffs
    def possCoeffs(partialEmb: Map[Int, Coeffs],
      newLabel: Int = 1,
      j: Int,
      symm: Symmetries
    ): Vector[(Coeffs, Label, Symmetries)] = {
      val norm = -q(j, j)
      val visited = partialEmb.keys // already assigned indices

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
                norm, cSymm)
            }
        }

      //println(s"implied: for j=$j (w=$norm) is ")
      //impliedCoeffs.foreach { println }
      // Extend implied coeffs to coefficients of new basis elements
      // so that the image has the correct self-pairing, then
      // recursively work out remaining coeffs
      val possibleCoeffs: Vector[(Coeffs, Label, Symmetries)] = 
      impliedCoeffs.flatMap { case (coeffs, cSymm) =>
        vectorsOfNorm(norm + coeffs.dot(coeffs), Some(maxRank  - coeffs.length)).map { v =>
          val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
            .filter(_._1 != 0) // don't want to include 0 coefficients
          val newSym: Symmetries = cSymm ++ symmetries(v).map(_.map(i => newLabel + i - 1))
          (fullCoeffs, newLabel + v.length, newSym)
        }
      }
      possibleCoeffs
    }

    // complete embedding in all possible ways
    def embed(partialEmb: Map[Int, Coeffs],
      newLabel: Int,
      symm: Symmetries
    ): Vector[Embedding] = {
      if (newLabel > maxRank + 1) {
        Vector()
      } else if (partialEmb.size == n) {
        Vector((0 until n).toVector.map(partialEmb(_)))
      } else if (partialEmb.isEmpty) {
        val j = (0 until n).minBy(i => -q(i, i))
        vectorsOfNorm(-q(j, j)) flatMap { seq =>
          val coeffs = seq zip (1 to seq.length)
          val newSym: Symmetries = symm ++ symmetries(seq).map(_.map(i => newLabel + i - 1))
          embed(Map(j -> coeffs), newLabel = seq.length + 1, newSym)
        }
      } else {
        // We want to assign coefficients to the vertex
        // with the least number of possibilities (branch factor)
        val visited = partialEmb.keys.toVector
        val unvisited = (0 until n).filter(i => !visited.contains(i)).toVector

        // possible coefficients for each unvisited
        val possCoeffsAllNodes: Vector[Vector[(Coeffs, Label, Symmetries)]] =
          for (i <- unvisited)
          yield possCoeffs(partialEmb, newLabel, i, symm)

        // index of possCoeffsAllNodes with minimum branch factor
        val i = possCoeffsAllNodes.map(_.length).zipWithIndex.min._2

        possCoeffsAllNodes(i).flatMap { case (coeffs, nextLabel, cSymm) =>
          embed(partialEmb + (unvisited(i) -> coeffs), nextLabel, cSymm)
        }
      }
    }
    // Sequences of increasing integers with norm norm
    // made up of exactly parts integers
    def changemaker(norm: Int, parts: Int) = {
      def loop(
        rem: Int = norm - 1,
        lenOfRest: Int = parts - 1,
        curr: Vector[Int] = Vector(1)
      ): Vector[Vector[Int]] = {
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

    // computing all possible changemaker coefficients and assign them first
    // NOTE: This method is slow if there are many possible changemaker coeffs.
    changemaker(homology, maxRank).flatMap { cm =>
      //println("Trying: " + cm)
      //println("Symmetries: " + symmetries(cm))
      val coeffs = cm.zipWithIndex.map({case (c_i, i) => (c_i, i+1)})
      embed(Map((maxRank-1) -> coeffs), newLabel = cm.length+1, symmetries(cm))
    }

    //embed(Map())
  }

  /* Finds all half-integer changemaker embeddings assuming that
   * the given lattice has no vectors of norm -1.
   */
  def halfIntCMEmbeddings(q0: IntersectionForm): Vector[Embedding] = {
    val homology = q0.det.toInt
    if (homology % 2 == 0) { // Can't be a half integer surgery
      Vector()
    } else {
      // homology = 2m + 1 for some m
      // then -homology/2 = [-(m+1), -2] = -(m+1) - 1/(-2).
      val m = (homology - 1)/2
      val q = q0.directSum(IntersectionForm(
        Vector(Vector(-(m+1), 1), Vector(1, -2))))
    val maxRank = q.rank
    val n = maxRank
    // All possible coefficients for basis j
    // Also returns newLabels for each choice of coeffs
    def possCoeffs(partialEmb: Map[Int, Coeffs],
      newLabel: Int = 1,
      j: Int,
      symm: Symmetries
    ): Vector[(Coeffs, Label, Symmetries)] = {
      val norm = -q(j, j)
      val visited = partialEmb.keys // already assigned indices

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
                norm, cSymm)
            }
        }

      //println(s"implied: for j=$j (w=$norm) is ")
      //impliedCoeffs.foreach { println }
      // Extend implied coeffs to coefficients of new basis elements
      // so that the image has the correct self-pairing, then
      // recursively work out remaining coeffs
      val possibleCoeffs: Vector[(Coeffs, Label, Symmetries)] = 
      impliedCoeffs.flatMap { case (coeffs, cSymm) =>
        vectorsOfNorm(norm + coeffs.dot(coeffs), Some(maxRank  - coeffs.length)).map { v =>
          val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
            .filter(_._1 != 0) // don't want to include 0 coefficients
          val newSym: Symmetries = cSymm ++ symmetries(v).map(_.map(i => newLabel + i - 1))
          (fullCoeffs, newLabel + v.length, newSym)
        }
      }
      possibleCoeffs
    }

    // complete embedding in all possible ways
    def embed(partialEmb: Map[Int, Coeffs],
      newLabel: Int,
      symm: Symmetries
    ): Vector[Embedding] = {
      if (newLabel > maxRank + 1) {
        Vector()
      } else if (partialEmb.size == n) {
        Vector((0 until n).toVector.map(partialEmb(_)))
      } else if (partialEmb.isEmpty) {
        val j = (0 until n).minBy(i => -q(i, i))
        vectorsOfNorm(-q(j, j)) flatMap { seq =>
          val coeffs = seq zip (1 to seq.length)
          val newSym: Symmetries = symm ++ symmetries(seq).map(_.map(i => newLabel + i - 1))
          embed(Map(j -> coeffs), newLabel = seq.length + 1, newSym)
        }
      } else {
        // We want to assign coefficients to the vertex
        // with the least number of possibilities (branch factor)
        val visited = partialEmb.keys.toVector
        val unvisited = (0 until n).filter(i => !visited.contains(i)).toVector

        // possible coefficients for each unvisited
        val possCoeffsAllNodes: Vector[Vector[(Coeffs, Label, Symmetries)]] =
          for (i <- unvisited)
          yield possCoeffs(partialEmb, newLabel, i, symm)

        // index of possCoeffsAllNodes with minimum branch factor
        val i = possCoeffsAllNodes.map(_.length).zipWithIndex.min._2

        possCoeffsAllNodes(i).flatMap { case (coeffs, nextLabel, cSymm) =>
          embed(partialEmb + (unvisited(i) -> coeffs), nextLabel, cSymm)
        }
      }
    }
    // Sequences of increasing integers with norm norm
    // made up of exactly parts integers
    def changemaker(norm: Int, parts: Int) = {
      def loop(
        rem: Int = norm - 1,
        lenOfRest: Int = parts - 1,
        curr: Vector[Int] = Vector(1)
      ): Vector[Vector[Int]] = {
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

    // computing all possible changemaker coefficients and assign them first
    // NOTE: This method is slow if there are many possible changemaker coeffs.
    /** See section 2.2 of "Alternating knots with unknotting number one" - McCoy
      * A half integer changemaker lattice is given by <pho, sigma>^perp in 
      * Z^n = Z^maxRank, where
      *  rho = e_1 - e_2 (note indices of our e's start at 1 compared to 0 in McCoy's paper),
      *  sigma = e_2 + sigma_1 e_3 + ... + sigma_r e_{r+2} where (sigma_1=1,...,sigma_r)
      *  is a changemaker vector.
      */
    // Enumerate sigma_1 e_1 + ... + sigma_r e_r which has norm |sigma| - 1.
    changemaker((m+1)-1, maxRank - 2).flatMap { cm =>
      //println("Trying: " + cm)
      //println("Symmetries: " + symmetries(cm))
      // coeffs of sigma
      val coeffs = cm.zipWithIndex.map({case (c_i, i) => (c_i, i+3)}) :+ ((1, 2)) // add e_2

      // first two e's, i.e. e_1, e_2 have no symmetries
      val symm = symmetries(cm).map(_.map(_ + 2)) ++ Vector(Vector(1), Vector(2))
      //println("Symmetries: " + symm)

      val initEmb = Map((maxRank-2) -> coeffs, (maxRank-1) -> Vector((-1,2), (1,1)))
      //println("Init emb: " + initEmb)
      embed(initEmb,
        newLabel = maxRank + 1,
        symm)
    }
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

  def embeddings(q: IntersectionForm, maxRank: Option[Int] = None): Stream[Embedding] = {
    LatticeEmbedding.embeddings(q, maxRank)
    /*
    val n = q.rank

    // All possible coefficients for vertex j
    // Also returns newLabels for each choice of coeffs
    def possCoeffs(partialEmb: Map[Int, Coeffs],
      newLabel: Int = 1,
      j: Int
    ): Vector[(Coeffs, Int)] = {
      val norm = -q(j, j)
      val visited = partialEmb.keys.toVector.sortBy(k => -q(k, k)) // already assigned indices

      // First work out all possible ways to assign coeffs with
      // already used labels by making sure we pair correctly
      // with previously visited generators
      val impliedCoeffs: Vector[Coeffs] =
        visited.foldLeft(Vector[Coeffs](Vector())) { (cs, i) =>
          cs.flatMap { c =>
            extendCoeffs(coeffs = c,
              nbrCoeffs = partialEmb(i),
              k = q(i, j),
              norm)
          }
        }
      //println(s"implied poss: ${impliedCoeffs.length} for norm: $norm")
      //println("partial: " + partialEmb)
      //println(impliedCoeffs.headOption)
      // Extend implied coeffs to coefficients of new basis elements
      // so that the image has the correct self-pairing, then
      // recursively work out remaining coeffs
      val possibleCoeffs: Vector[(Coeffs, Int)] = 
      impliedCoeffs.flatMap { coeffs =>
        vectorsOfNorm(norm + coeffs.dot(coeffs), maxRank.map(_ - coeffs.length)).map { v =>
          val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
            .filter(_._1 != 0) // don't want to include 0 coefficients
          (fullCoeffs, newLabel + v.length)
        }
      }
      //println("branch: " + possibleCoeffs.length)
      //assert(possibleCoeffs.length < 40,
      //  s"found: ${possibleCoeffs.length}\n$partialEmb\n${possibleCoeffs.head}")
      possibleCoeffs
    }

    // complete embedding in all possible ways
    def embed(partialEmb: Map[Int, Coeffs],
              newLabel: Int = 1
    ): Vector[Embedding] = {
      if (maxRank.map(newLabel > _ + 1).getOrElse(false)) {
        Vector()
      } else if (partialEmb.size == n) {
        Vector((0 until n).toVector.map(partialEmb(_)))
      } else if (partialEmb.isEmpty) {
        val j = (0 until n).minBy(i => -q(i, i))
        vectorsOfNorm(-q(j, j)) flatMap { seq =>
          val coeffs = seq zip (1 to seq.length)
          embed(Map(j -> coeffs), newLabel = seq.length + 1)
        }
      } else {
        // We want to assign coefficients to the vertex
        // with the least number of possibilities (branch factor)
        val visited = partialEmb.keys.toVector
        val unvisited = (0 until n).filter(i => !visited.contains(i)).toVector

        // possible coefficients for each unvisited
        val possCoeffsAllNodes: Vector[Vector[(Coeffs, Int)]] =
          for (i <- unvisited)
          yield possCoeffs(partialEmb, newLabel, i)

        // index of possCoeffsAllNodes with minimum branch factor
        val i = possCoeffsAllNodes.map(_.length).zipWithIndex.min._2
        //println(s"Branch options: ${possCoeffsAllNodes.map(_.length)}")
        //println(s"Selecting branch: ${possCoeffsAllNodes(i).length}")
        possCoeffsAllNodes(i).flatMap { case (coeffs, nextLabel) =>
          embed(partialEmb + (unvisited(i) -> coeffs), nextLabel)
        }
      }
    }
    embed(Map())
     */
  }

  /**
    * 
    * Enumerate embeddings, if method takes more than `numMillis` then 
    * break out and return None.
    */
  def embeddingsMaxDuration(
    numMillis: Long,
    q: IntersectionForm,
    maxRank: Option[Int] = None): Option[Stream[Embedding]] = {
    EmbeddingWithDuration.embeddingsMaxDuration(numMillis, q, maxRank)
    /*
    val initTimeMillis = System.nanoTime() / 1000000L
    val n = q.rank

    // All possible coefficients for vertex j
    // Also returns newLabels for each choice of coeffs
    def possCoeffs(partialEmb: Map[Int, Coeffs],
      newLabel: Int = 1,
      j: Int
    ): Vector[(Coeffs, Int)] = {
      val currTimeMillis = System.nanoTime() / 1000000L
      if (currTimeMillis - initTimeMillis > numMillis) {
        Vector()
      } else {
      val norm = -q(j, j)
      val visited = partialEmb.keys.toVector.sortBy(k => -q(k,k)) // already assigned indices

      // First work out all possible ways to assign coeffs with
      // already used labels by making sure we pair correctly
      // with previously visited generators
      val impliedCoeffs: Vector[Coeffs] =
        visited.foldLeft(Vector[Coeffs](Vector())) { (cs, i) =>
          cs.flatMap { c =>
            val remTime = numMillis - (System.nanoTime() / 1000000L - initTimeMillis)
            extendCoeffsMaxDuration(
              System.nanoTime()/1000000L,
              remTime,
              coeffs = c,
              nbrCoeffs = partialEmb(i),
              k = q(i, j),
              norm).getOrElse(Vector())
          }
        }

        if (System.nanoTime() / 1000000L - initTimeMillis > numMillis) Vector() else {
          // Extend implied coeffs to coefficients of new basis elements
          // so that the image has the correct self-pairing, then
          // recursively work out remaining coeffs
          val possibleCoeffs: Vector[(Coeffs, Int)] =
            impliedCoeffs.flatMap { coeffs =>
              val remTime = numMillis - (System.nanoTime()/1000000L - initTimeMillis)
              vectorsOfNormMaxDuration(remTime,
                norm + coeffs.dot(coeffs), maxRank.map(_ - coeffs.length))
                .getOrElse(Vector())
                .map { v =>
                val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
                  .filter(_._1 != 0) // don't want to include 0 coefficients
                (fullCoeffs, newLabel + v.length)
              }
            }
          if (System.nanoTime() / 1000000L - initTimeMillis > numMillis) Vector()
          else possibleCoeffs
        }
      }
    }

    // complete embedding in all possible ways
    def embed(partialEmb: Map[Int, Coeffs],
              newLabel: Int = 1
    ): Option[Vector[Embedding]] = {
      val currTimeMillis = System.nanoTime() / 1000000L
      if (currTimeMillis - initTimeMillis > numMillis) {
        None
      } else if (maxRank.map(newLabel > _ + 1).getOrElse(false)) {
        Some(Vector())
      } else if (partialEmb.size == n) {
        Some(Vector((0 until n).toVector.map(partialEmb(_))))
      } else if (partialEmb.isEmpty) {
        val j = (0 until n).minBy(i => -q(i, i))
        val remTime = numMillis - (System.nanoTime()/1000000L - initTimeMillis)
        val res = vectorsOfNormMaxDuration(remTime, -q(j, j)).getOrElse(Vector())
          .flatMap({ seq =>
            val coeffs = seq zip (1 to seq.length)
            embed(Map(j -> coeffs), newLabel = seq.length + 1).getOrElse(Vector())
          })
        if (System.nanoTime()/1000000L - initTimeMillis > numMillis) None else Some(res)
      } else {
        // We want to assign coefficients to the vertex
        // with the least number of possibilities (branch factor)
        val visited = partialEmb.keys.toVector
        val unvisited = (0 until n).filter(i => !visited.contains(i)).toVector

        // possible coefficients for each unvisited
        val possCoeffsAllNodes: Vector[Vector[(Coeffs, Int)]] =
          for (i <- unvisited)
          yield possCoeffs(partialEmb, newLabel, i)

        if (System.nanoTime()/1000000L - initTimeMillis < numMillis) {
          // index of possCoeffsAllNodes with minimum branch factor
          val i = possCoeffsAllNodes.map(_.length).zipWithIndex.min._2

          val res = possCoeffsAllNodes(i).flatMap { case (coeffs, nextLabel) =>
            embed(partialEmb + (unvisited(i) -> coeffs), nextLabel).getOrElse(Vector())
          }
          if (System.nanoTime()/1000000L - initTimeMillis > numMillis) None else Some(res)
        } else None
      }
    }
    embed(Map())
     */
  }

  /* Simpler but runs slow!
  def embeddings(q: IntersectionForm): Vector[Embedding] = {
    val n = q.rank
    // complete embedding in all possible ways
    def embed(currEmb: Embedding, newLabel: Int = 1): Vector[Embedding] = {
      if (currEmb.length == n) Vector(currEmb)
      else if (currEmb.isEmpty) {
        vectorsOfNorm(-q(0, 0)) flatMap { seq =>
          val coeffs = seq zip (1 to seq.length)
          embed(currEmb = Vector(coeffs), newLabel = seq.length + 1)
        }
      } else {
        val j = currEmb.length
        val norm = -q(j, j)
        // First work out all possible ways to assign coeffs with
        // already used labels by making sure we pair correctly
        // with previously visited generators
        val impliedCoeffs: Vector[Coeffs] =
          (0 until currEmb.length).foldLeft(Vector[Coeffs](Vector())) { (cs, i) =>
            cs.flatMap { c =>
              extendCoeffs(coeffs = c,
                nbrCoeffs = currEmb(i),
                k = q(i, j),
                norm)
            }
          }

        // Extend implied coeffs to coefficients of new basis elements
        // so that the image has the correct self-pairing, then
        // recursively work out remaining coeffs
        val embeddings: Vector[Embedding] = 
        impliedCoeffs.flatMap { coeffs =>
          vectorsOfNorm(norm + coeffs.dot(coeffs)).flatMap { v =>
            val fullCoeffs = (coeffs ++ v.zip(Stream.from(newLabel)))
              .filter(_._1 != 0) // don't want to include 0 coefficients
            embed(currEmb :+ fullCoeffs, newLabel + v.length)
          }
        }
        embeddings
      }    
    }
    embed(currEmb = Vector())
  }
  */

  implicit class RichCoeffs(c: Coeffs) {
    /**
     * returns dot product, assuming coeffs are basis for
     *         std negative definite lattice.
     */
    def dot(c2: Coeffs): Int = {
      if (c.isEmpty || c2.isEmpty) 0
      else {
        val m = max(c2.map(_._2).max, c.map(_._2).max) + 1
        val arr: Array[Int] = Array.fill[Int](m)(0)
        val arr2 = Array.fill[Int](m)(0)
        c.foreach { case (n, i) => arr(i) = n }
        c2.foreach { case (n, i) => arr2(i) = n }
        (0 until arr.length).map(i => -arr(i)*arr2(i)).sum
      }

      /*
      c.map {
        case (a, n) => {
          c2.find(_._2 == n) match {
            case Some((b, _)) => -1 * a * b
            case None => 0
          }
        }
      }.sum
       */
    }

    /** Absolute value of self pairing. */
    def norm: Int = -1 * dot(c)
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

  /**
    *  Sequences of non-increasing positive integers with norm given by
    *  norm, where the length of the sequence is at most m.
    * 
    *  Enumerate but don't take longer than `millis` milliseconds (return None if so).
    */
  def vectorsOfNormMaxDuration(millis: Long, norm: Int, m: Int): Option[Vector[Vector[Int]]] = {
    val initTimeMillis = System.nanoTime() / 1000000L
    def loop(
        rem: Int = norm,
        maxInRest: Int = norm,
        lenOfRest: Int = m
    ): Option[Vector[Vector[Int]]] = {
      if (System.nanoTime()/1000000L - initTimeMillis > millis) None
      else if (rem == 0 && lenOfRest >= 0) Some(Vector(Vector()))
      else if (lenOfRest < 0 || (lenOfRest == 0 && rem > 0)) Some(Vector())
      else {
        val n = min(maxInRest, sqrt(rem.toDouble).toInt)
        val res = for (
          i <- (1 to n).toVector if (System.nanoTime()/1000000L - initTimeMillis < millis);
          lst <- loop(rem - i * i, i, lenOfRest - 1).getOrElse(Vector())
        ) yield (i +: lst)
        if (System.nanoTime()/1000000L - initTimeMillis > millis) None else Some(res)
      }
    }
    loop()
  }

  def vectorsOfNormMaxDuration(
    millis: Long, norm: Int, m: Option[Int]): Option[Vector[Vector[Int]]] = m match {
    case Some(maxRank) => vectorsOfNormMaxDuration(millis, norm, maxRank)
    case None => vectorsOfNormMaxDuration(millis, norm)
  }

  /**
    * Sequences of non-increasing positive integers with norm given
    * by norm.
    */
  def vectorsOfNormMaxDuration(millis: Long, norm: Int): Option[Vector[Vector[Int]]] = {
    val initTimeMillis = System.nanoTime()/1000000L
      def loop(
        rem: Int = norm,
        maxInRest: Int = norm
      ): Option[Vector[Vector[Int]]] = {
        if (System.nanoTime()/1000000L - initTimeMillis > millis) None
        else if (rem == 0) Some(Vector(Vector()))
        else {
          val n = min(maxInRest, sqrt(rem.toDouble).toInt)
          val res = for (
            i <- (1 to n).toVector if (System.nanoTime()/1000000L - initTimeMillis < millis);
            lst <- loop(rem - i * i, i).getOrElse(Vector())
          ) yield (i +: lst)
          if (System.nanoTime()/1000000L - initTimeMillis > millis) None else Some(res)
        }
      }
    loop()
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
      if (coeffs.dot(nbrCoeffs) == k) Vector((coeffs, symm)) else Vector()
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
            val newCoeffs: Coeffs = coeffs ++ seq.zip(symmSet)
            val newNorm = norm - seq.map(i => i*i).sum
            val newKTarget = k + a*seq.sum

            val newSymm: Symmetries = symmRest ++ symmetries(seq).map(_.map(i => symmSet(i-1)))
            extendCoeffs(newCoeffs, nbrCoeffsRest, newKTarget, newNorm, newSymm)
          }
        }
      }
    }
  }


  /**
   * When we know some of the coefficients of an embedding
   * of a node and we want work out more coefficients using
   * the condition that Q(node, some other node) = k and
   * Q(node, node) <= norm
   * @param coeffs Coefficients which we only partially know.
   * @param nbrCoeffs Want Q(coeffs, nbrCoeffs) = k.
    */
  var calls = 0
  def extendCoeffs(
    coeffs: Coeffs,
    nbrCoeffs: Coeffs,
    k: Int,
    norm: Int
  ): Vector[Coeffs] = {
    calls += 1
    if (calls % 1000000 == 0) println(calls)
    if (norm < 0) Vector()
    else if (norm == 0 || nbrCoeffs.isEmpty) {
      if (coeffs.dot(nbrCoeffs) == k)
        Vector(coeffs)
      else
        Vector()
    } else {
      // e_n is basis element we're working with
      val (a, e_n) = nbrCoeffs(0) // nbrCoeffs is not empty
      coeffs.find(_._2 == e_n) match {
        case Some((b, _)) => // already assigned a coefficient of e_n
          extendCoeffs(
            coeffs,
            nbrCoeffs.tail,
            k + a * b,
            norm
          )
        case None => { // loop over all possible coefficients of e_n
          val m: Int = sqrt(norm.toDouble).round.toInt
            (-m to m).toVector.flatMap(i =>
                extendCoeffs(
                  (i, e_n) +: coeffs,
                  nbrCoeffs.tail,
                  k + a*i,
                  norm - i*i
                )
            )
        }
      }
    }
  }

  /**
   * When we know some of the coefficients of an embedding
   * of a node and we want work out more coefficients using
   * the condition that Q(node, some other node) = k and
   * Q(node, node) <= norm
   * @param coeffs Coefficients which we only partially know.
   * @param nbrCoeffs Want Q(coeffs, nbrCoeffs) = k.
   */
  def extendCoeffsMaxDuration(
    initTimeMillis: Long,
    millis: Long,
    coeffs: Coeffs,
    nbrCoeffs: Coeffs,
    k: Int,
    norm: Int
  ): Option[Vector[Coeffs]] = {
    if (System.nanoTime()/1000000L - initTimeMillis > millis) None
    else if (norm < 0) Some(Vector())
    else if (norm == 0 || nbrCoeffs.isEmpty) {
      if (coeffs.dot(nbrCoeffs) == k)
        Some(Vector(coeffs))
      else
        Some(Vector())
    } else {
      // e_n is basis element we're working with
      val (a, e_n) = nbrCoeffs(0) // nbrCoeffs is not empty
      coeffs.find(_._2 == e_n) match {
        case Some((b, _)) => // already assigned a coefficient of e_n
          val res = extendCoeffsMaxDuration(
            initTimeMillis,
            millis,
            coeffs,
            nbrCoeffs.tail,
            k + a * b,
            norm
          ).getOrElse(Vector())
          if (System.nanoTime()/1000000L - initTimeMillis > millis) None else Some(res)
        case None => { // loop over all possible coefficients of e_n
          val remTime = millis - (System.nanoTime()/1000000L - initTimeMillis)
          val m: Int = sqrt(norm.toDouble).round.toInt
            val res = (-m to m).toVector.flatMap(i =>
              extendCoeffsMaxDuration(
                  initTimeMillis,
                  millis,
                  (i, e_n) +: coeffs,
                  nbrCoeffs.tail,
                  k + a*i,
                  norm - i*i
                ).getOrElse(Vector())
            )
          if (System.nanoTime()/1000000L - initTimeMillis > millis) None else Some(res)
        }
      }
    }
  }
}

