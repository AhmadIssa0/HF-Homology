package ahmad.hfhomology

import scala.annotation.tailrec
import spire.implicits._
import spire.math._

/**  We consider the following question:
  * 
  *  Consider C (depending on k) such that if q_1/p_1 + ... + q_k/p_k < C then
  *  the Seifert fibered space SFS(1; p_1/q_1, ..., p_k/q_k) has plumbing
  *  which embeds into a diagonal lattice.
  * 
  *  What is the maximum such C (as a function of k)?
  * 
  */
object EmbeddingConstant {
  /** The points (q_1/p_1, ..., q_k/p_k) in Q^k satisfying:
    * q_1/p_1 + ... + q_k/p_k <= 1 parameterise the Seifert fibered spaces
    * bounding a positive (semi-)definite lattice.
    * This is a rational simplex in R^k.
    */

  def gapFillingAlongArcs(initKnownEmbeddingPts: Vector[Vector[Rational]] = Vector(Vector(r"1/3", r"1/3", r"1/3"))) = {
    type Point = Vector[Rational]
    
    // p cube strictly covers p2
    def strictlyCovers(p: Point, p2: Point): Boolean =
      p != p2 && (0 until p.length).forall(i => p(i) > p2(i))

    def dist(p1: Point, p2: Point) =
      (0 until p1.length).map(i => (p1(i) - p2(i))**2).qsum

    def toSFS(p: Point): SFSOverS2 =
      SFSOverS2(-1, p.map(r => -1/r))

    def hasEmbedding(p: Point): Boolean =
      !toSFS(p).toTree.toIntersectionForm.embeddings().isEmpty

    def embeddings(p: Point, maxTimeMillis: Long) =
      toSFS(p).toTree.toIntersectionForm.embeddingsMaxDuration(maxTimeMillis)

    def diagonalPtOnTri(p: Point): Point = {
      val t = p.qsum
      (0 until p.length).toVector.map(i => p(i) + (1 - t)/p.length)
    }

    var usedPts: Vector[Vector[Rational]] = initKnownEmbeddingPts
    var improved: Boolean = true
    while (improved) {
      val notCovered = EmbeddingConstant.cubesMinimum(usedPts)
      println(s"best: ${notCovered.qsum} $notCovered ${notCovered.qsum.toDouble} usedPts size: ${usedPts.length}")
      usedPts = usedPts.filter(p => p.qsum > notCovered.qsum)
      /*if (embeddings(diagonalPtOnTri(notCovered), 1000).map(_.isEmpty).getOrElse(false)) {
        usedPts = usedPts :+ diagonalPtOnTri(notCovered)
      } else {*/
        (2 until 400)
          .filter(i => notCovered.forall { r => i != r })
          .map(i => notCovered.map(r =>
            if (r == 0) Rational(1, i) else 1/(1/r - Rational(1, i))))
          .map(p => p.map(_.limitTo(500)))
          .filter(p => strictlyCovers(p, notCovered) && p.forall { c => c > 0 && c < 1 })
          .find(p => { println(s"trying: $p");
            embeddings(p, 2000).map(!_.isEmpty).getOrElse(false) }) match {
          case Some(p) => {
            usedPts = usedPts :+ p
          }
          case None => {
            println(s"Can't cover $notCovered")
            println(s"best: ${notCovered.qsum} $notCovered ${notCovered.qsum.toDouble} usedPts size: ${usedPts.length}")
            improved = false
          }
        }
      //}
    }
    //println(s"usedPts: $usedPts")
    usedPts
  }

  def gapFilling(maxNumer: Int) = {
    type Point = Vector[Rational]

    var allPts: List[Vector[Rational]] = List()
    for (
      a1 <- 2 to maxNumer; b1 <- 1 until a1 if gcd(a1,b1) == 1
      ;a2 <- 2 to maxNumer; b2 <- 1 until a2 if gcd(a2,b2) == 1 && a1*b2 >= a2*b1
      //;a3 <- 2 to maxNumer; b3 <- 1 until a3 if gcd(a3,b3) == 1 && a2*b3 >= a3*b2
) {
      val r1 = Rational(a1, b1)
      val r2 = Rational(a2, b2)
      //val r3 = Rational(a3, b3)
      if (1 - 1/r1 - 1/r2 > 0) {
        val r3 = 1/(1 - 1/r1 - 1/r2)
        if (r3 <= r2 && r3.numerator <= maxNumer)
          allPts = Vector(1/r1,1/r2,1/r3) :: allPts
      }
    }
    println(s"Number of points in consideration: ${allPts.length}")
    
    // p cube strictly covers p2
    def strictlyCovers(p: Point, p2: Point): Boolean =
      p != p2 && (0 until p.length).forall(i => p(i) > p2(i))

    def dist(p1: Point, p2: Point) =
      (0 until p1.length).map(i => (p1(i) - p2(i))**2).qsum

    def toSFS(p: Point): SFSOverS2 =
      SFSOverS2(-1, p.map(r => -1/r))

    def hasEmbedding(p: Point): Boolean =
      !toSFS(p).toTree.toIntersectionForm.embeddings().isEmpty

    def diagonalPtOnTri(p: Point): Point = {
      val t = p.qsum
      (0 until p.length).toVector.map(i => p(i) + (1 - t)/p.length)
    }

    var usedPts: Vector[Vector[Rational]] = Vector(Vector(r"1/3", r"1/3", r"1/3"))
    var improved: Boolean = true
    while (improved) {
      val notCovered = EmbeddingConstant.cubesMinimum(usedPts)
      println(s"best: ${notCovered.qsum} $notCovered ${notCovered.qsum.toDouble}") 
      val candidatePts = 
      allPts.toStream.filter(p => strictlyCovers(p, notCovered))
        .sortBy(p => dist(p, diagonalPtOnTri(notCovered)))
      var i = 0
      var dontEmbed: List[Point] = List()
      candidatePts.find({ p =>
        //println(s"Checking embedding of $p")
        i = i + 1
        if (i % 100 == 0)
          println(i)
        val hasEmb = hasEmbedding(p)
        //println(s"Embeds? $p: $hasEmb")
        //println(s"best: ${notCovered.qsum} $notCovered ${notCovered.qsum.toDouble}") 
        if (! hasEmb) dontEmbed = p :: dontEmbed //allPts = allPts.filter(p2 => p2 != p)
        hasEmb
      }) match {
        case Some(p) => usedPts = usedPts :+ p
        case None => {
          println(s"ending, couldn't cover: $notCovered")
          improved = false
        }
      }
      allPts = allPts.filter(p => !dontEmbed.contains(p))
      //assert(!usedPts.contains(Vector(r"1/4", r"1/4", r"1/2")), s"$usedPts")
      //println(s"Used pts: ${usedPts.reverse.take(10)}")
    }
    //println(s"usedPts: $usedPts")
    usedPts
  }

  /**
    * Using `cubeCorners` determines maximum C such that if 
    * q_1/p_1 + ... + q_k/p_k < C then SFS(1; p_1/q_1, ..., p_k/q_k) has a 
    * lattice embedding.
    * 
    * Uses the fact that if p is a point in `cubeCorners` then
    * any point p' with p'(i) <= p(i) (i-th coordinate) for all i, also
    * has a lattice embedding.
    * 
    * @param cubeCorners Vector of Rational points known to have lattice embeddings.
    */
  def cubesMinimum(cubeCorners: Vector[Vector[Rational]]) = {
    if (cubeCorners.isEmpty) Vector()
    else {
      /**  Want point on union of cubes for which sum q_i/p_i is maximal.
        *  This will occur at some intersection of three planes.
        */
      val k = cubeCorners.head.length

      // By symmetry work in the region with q_1/p_1 <= q_2/p_2 <= ... <= q_k/p_k.
      // Also add in points (1,1,0), (0,1,1), (1,0,1) as the walls representing
      // the condition that all coordinates are non-negative.
      /*
      val wallPts = for (i <- (0 until k).toVector) yield {
        Vector.fill(k)(r"1").updated(i, r"0")
      }*/

      //val ordEmbPts = (wallPts ++ cubeCorners.map(p => p.sorted).flatMap(_.permutations.toVector)).distinct
      val ordEmbPts = Vector.fill(k)(r"0") +: cubeCorners.map(p => p.sorted)
      //println("ordEmbPts length: " + ordEmbPts.length)
      //println(ordEmbPts)

      def optimal(currWalls: Vector[Vector[Rational]], currSmallest: Rational
      ): Option[Vector[Rational]] = {
        val j = currWalls.length
        val currSize: Rational = (0 until j).map(i => currWalls(i)(i)).qsum
        val minimalExtensionSize: Rational =
          if (j > 0) currWalls(j-1)(j-1) * (k-j) else r"0"

        if (currSize + minimalExtensionSize >= currSmallest) {
          None
        } else if (currWalls.length == k) {
          val pt = for (i <- (0 until k).toVector) yield (currWalls(i)(i))
          //println("preconsidering: " + pt)
          if (! ordEmbPts.exists(p => (0 until k).forall(j => p(j) > pt(j)))) {
            //println("considering: " + pt)
            Some(pt)
          } else {
            //println(ordEmbPts.find(p => (0 until k).forall(j => p(j) >= pt(j))))
            None
          }
        } else {
          val i = currWalls.length
          val extraPoss = (0 until k).toVector.map({
            case j if j < i => currWalls(j)(j)
            case _ => if (i > 0) currWalls(i-1)(i-1) else r"0"
          })
          var smallest = Vector.fill(k)(r"1")
          for (p <- ordEmbPts :+ extraPoss) {
            if ((i == 0 || currWalls(i-1)(i-1) <= p(i)) // point in symmetry region
                //&& currWalls.forall(wall => wall(i) > p(i)) &&
                //currWalls.zipWithIndex.forall({ case (wall, j) => wall(j) < p(j) })
            ) {
              val walls = currWalls :+ p
              val localSmallest = optimal(walls, min(currSmallest, smallest.qsum))
                                  .getOrElse(smallest)
              if (localSmallest.qsum < smallest.qsum) smallest = localSmallest
            }
          }
          if (smallest == Vector.fill(k)(r"1")) None
          else Some(smallest)
        }
      }
      optimal(Vector(), r"1").getOrElse(Vector.fill(k)(r"0"))
    }
  }

  def impliesPointEmbeds(pt: Vector[Rational], hasEmb: Vector[Vector[Rational]]) = {
    val ordPt = pt.sorted
    hasEmb.exists(p => ordPt < p.sorted)
  }

  /**
    *  Answers: is it true that for all sum q_i/p_i <= c there is a lattice embedding,
    *  using the information that points of the form (q_1/p_1,...,q_n/p_n) 
    *  in `hasEmb` are known to have lattice embeddings.
    * 
    *  Suppose we want to verify that for sum q_i/p_i <= c there is a lattice embedding.
    *  Use the known embedding points in `cubeCorners` to compute the implied
    *  embedding region on the hyperplane sum x_i = c (this region will be a triangle).
    * 
    *  Now we want to check that these simplices cover the big simplex in the
    *  hyperplane sum x_i = c.
    */
  def lowerbound(hasEmb: Vector[Vector[Rational]], c: Rational) = {
    // `p` implies a simplex in hyperplane sum x_i = c embeds.
    // returns vertices of this simplex
    def project(p: Vector[Rational]): Vector[Vector[Rational]] = {
      (0 until p.length).toVector.map(i =>
        p.updated(i, p(i) - (1 - c))
      )
    }

    type Point = Vector[Rational]
    type Simplex = Vector[Vector[Rational]]

    // We want to solve A.x = b where
    // val b = RatMatrix(Vector(p :+ r"1")).transpose
    // val A = RatMatrix(simp).transpose.addConstantRows(1, r"1").
    // x = (A^t A)^-1 A^t b
    // x gives the least squares solution, i.e. minimises ||A.x - b||
    // `simpMat` is (A^t A)^-1 A^t.    
    def isPointInSimp(p: Point, simp: Simplex,
      simpMat: Option[RatMatrix] = None): Boolean = {
      simpMat match {
        case None => {
          val b = RatMatrix(Vector(p :+ r"1")).transpose
          val A = RatMatrix(simp).transpose.addConstantRows(1, r"1")
          // Equation we want to solve is A.x = b
          // then we check all coordinates of x are in range [0,1].
          //println(s"Equation: A=$A\n b=$b")
          assert(A.mat.forall(row => row.forall(r => r.denominator < SafeLong(10)**10)))
          A.solve(b) match {
            case Left(_) => false
            case Right(x) => {
              //println(s"Coeffs: $x")
              x.transpose.mat(0).forall(coord => coord >= 0 && coord <= 1)
            }
          }
        }
        case Some(x) => {
          val b = RatMatrix(Vector(p :+ r"1")).transpose
          (x * b).transpose.mat(0).forall(coord => coord >= 0 && coord <= 1)
        }
      }
    }

    // Computes matrix (A^t A)^-1 A^t (see `isPointInSimp` function)
    def leastSquaresMatrix(simp: Simplex): RatMatrix = {
      val A = RatMatrix(simp).transpose.addConstantRows(1, r"1")

      (A.transpose * A).inverse match {
        case Right(x) => x * A.transpose
        case Left(x) => {
          throw new Exception(s"Non-invertible matrix. Simplex is degenerate: $x")
        }

      }
    }


    // is `simp1` contained in `simp2`?
    def isSimpInSimp(simp1: Simplex, simp2: Simplex,
      simp2Mat: Option[RatMatrix] = None): Boolean = {
      // Check if all points of simp1 are in simp2
      simp1.forall(p => isPointInSimp(p, simp2, simp2Mat))
    }

    def addPoints(p1: Point, p2: Point): Point =
          (0 until p1.length).toVector.map(i => p1(i) + p2(i))

    def subtractPoints(p1: Point, p2: Point): Point =
      (0 until p1.length).toVector.map(i => p1(i) - p2(i))

    // Return subsimplices which cover `simp`
    def coveringSubSimps(simp: Simplex): Vector[Simplex] = {
      val n = simp.length - 1 // dimension of simplex
      val scale = 1.0*n/(n+1) // (dist vert to center)/(vert to ctr of opp face)
      simp.map({ origin =>
        simp.map(p => addPoints(subtractPoints(p, origin).map(_*scale), origin))
      })
    }

    // do the simplices in `cover` cover the entire simplex `simp`
    // `cover` also requires `leastSquaresMatrix` to be passed (speeds up computation).
    var calls = 0
    def covers(cover: Vector[(Simplex, RatMatrix)], simp: Simplex): Boolean = {
      calls = calls + 1
      if (calls % 10 == 0) {
        println(s"calls: $calls")

        //if (calls > 1000)
        //  sys.exit(1)
      }

      if (cover.exists({ case (s, mat) => isSimpInSimp(simp, s, Some(mat)) })) {
        true
      } else {
        // barycentric subdivide and recursively call
        // for n simplex this creates (n+1)! subsimplices
        // If v_0,..., v_n are the vertices of the simplex.
        // Then any permutation p_0, ..., p_n defines a subsimplex by
        // taking the vertices to be the barycenters of p_0,...,p_i for all i
        val n = simp.length - 1


        coveringSubSimps(simp).forall ({ subSimp =>
          val pointsCovered = subSimp.forall(p =>
            cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
          )
          if (! pointsCovered) {
            println(
            subSimp.find(p =>
              ! cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
            )
            )
          }
          pointsCovered && covers(cover, subSimp)
        })
        /*
        simp.permutations.forall({ perm =>
          val partialSums = perm.scanLeft(Vector.fill(n+1)(r"0"))(addPoints).drop(1)
          val subSimp = (0 until n+1)
            .map(i => partialSums(i).map(_ / (i+1))).toVector
          //println(s"subSimp: $subSimp")
          // check if all vertices are covered
          val pointsCovered = subSimp.forall(p =>
            cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
          )
          if (! pointsCovered) {
            println(
            subSimp.find(p =>
              ! cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
            )
            )
          }
          if (! pointsCovered) {
            false
          } else {
            /*
            val newCover = cover.filter(s =>
              s.exists(p => isPointInSimp(p, subSimp)) ||
              subSimp.exists(p => isPointInSimp(p, s))
              )*/
            covers(cover, subSimp)
          }
          //pointsCovered && covers(cover, subSimp)
        })*/
      }
    }

    if (hasEmb.length == 0) {
      c <= 0
    } else {
      val cover = hasEmb.filter(p => p.qsum > c)
        .map({ p =>
          val simp = project(p)
          (simp, leastSquaresMatrix(simp))
        })
      val n = hasEmb.head.length
      val simp = (0 until n).toVector
        .map(i => Vector.tabulate(n)({
          case `i` => c
          case _ => r"0"
        }))
      
      val partialSums = simp.scanLeft(Vector.fill(n)(r"0"))(addPoints).drop(1)
      val subSimp = (0 until n)
            .map(i => partialSums(i).map(_ / (i+1))).toVector
      //println(s"cover: $cover\nsimp: $simp")
      covers(cover, subSimp)
    }
  }

  
  def lowerboundBigDecimal(hasEmb: Vector[Vector[Rational]], c: BigDecimal) = {
    val mc = new java.math.MathContext(34)
    val tol = BigDecimal("0.1") ** 20
    val one = r"1".toBigDecimal(mc)
    val zero = r"0".toBigDecimal(mc)
    // `p` implies a simplex in hyperplane sum x_i = c embeds.
    // returns vertices of this simplex
    def project(p: Vector[Rational]): Vector[Vector[BigDecimal]] = {
      (0 until p.length).toVector.map(i =>
        p.updated(i, p(i) - (1 - c)).map(_.toBigDecimal(mc))
      )
    }

    type Point = Vector[BigDecimal]
    type Simplex = Vector[Vector[BigDecimal]]
    type DMatrix = FieldMatrix[BigDecimal]
    // We want to solve A.x = b where
    // val b = RatMatrix(Vector(p :+ r"1")).transpose
    // val A = RatMatrix(simp).transpose.addConstantRows(1, r"1").
    // x = (A^t A)^-1 A^t b
    // x gives the least squares solution, i.e. minimises ||A.x - b||
    // `simpMat` is ((A^t A)^-1 A^t)^t.    
    def isPointInSimp(p: Point, simp: Simplex,
      simpMat: Option[DMatrix]): Boolean = {
      simpMat match {
        case None => {
          val b = FieldMatrix[BigDecimal](Vector(p :+ one)).transpose
          val A = FieldMatrix[BigDecimal](simp).transpose.addConstantRows(1, one)
          // Equation we want to solve is A.x = b
          // then we check all coordinates of x are in range [0,1].
          //println(s"Equation: A=$A\n b=$b")
          A.solveApprox(b, tol) match {
            case Left(_) => false
            case Right(x) => {
              //println(s"Coeffs: $x")
              x.transpose.mat(0).forall(coord => coord >= 0 && coord <= 1)
            }
          }
        }
        case Some(x) => {
          val b_trans = FieldMatrix[BigDecimal](Vector(p :+ one))
          //  (x * b).transpose.mat(0).forall(coord => coord >= 0 && coord <= 1)
          (b_trans * x).mat(0).forall(coord => coord >= 0 && coord <= 1)
        }
      }
    }

    // Computes matrix ((A^t A)^-1 A^t)^t (see `isPointInSimp` function)
    def leastSquaresMatrix(simp: Simplex): DMatrix = {
      val A = FieldMatrix[BigDecimal](simp).transpose.addConstantRows(1, one)

      (A.transpose * A).inverseApprox(tol) match {
        case Right(x) => A * x.transpose //x * A.transpose
        case Left(x) => {
          throw new Exception(s"Non-invertible matrix. Simplex is degenerate: $x")
        }
      }
    }


    // is `simp1` contained in `simp2`?
    def isSimpInSimp(simp1: Simplex, simp2: Simplex,
      simp2Mat: Option[DMatrix] = None): Boolean = {
      // Check if all points of simp1 are in simp2
      simp1.forall(p => isPointInSimp(p, simp2, simp2Mat))
    }

    def addPoints(p1: Point, p2: Point): Point =
      (0 until p1.length).toVector.map(i => p1(i) + p2(i))

    def subtractPoints(p1: Point, p2: Point): Point =
          (0 until p1.length).toVector.map(i => p1(i) - p2(i))

    // Return subsimplices which cover `simp`
    def coveringSubSimps(simp: Simplex): Vector[Simplex] = {
      val n = simp.length - 1 // dimension of simplex
      val scale = Rational(n,(n+1)).toBigDecimal(mc) // (dist vert to center)/(vert to ctr of opp face)
      simp.map({ origin =>
        simp.map(p => addPoints(subtractPoints(p, origin).map(_*scale), origin))
      })
    }

    // do the simplices in `cover` cover the entire simplex `simp`
    // `cover` also requires `leastSquaresMatrix` to be passed (speeds up computation).
    //@tailrec
    var calls = 0
    def covers(cover: Vector[(Simplex, DMatrix)], simp: Simplex): Boolean = {
      calls = calls + 1
      if (calls % 10 == 0) {
        println(s"calls: $calls")
        //if (calls > 10000)
        //  sys.exit(1)
      }

      if (cover.exists({ case (s, mat) => isSimpInSimp(simp, s, Some(mat)) })) {
        true
      } else {
        // barycentric subdivide and recursively call
        // for n simplex this creates (n+1)! subsimplices
        // If v_0,..., v_n are the vertices of the simplex.
        // Then any permutation p_0, ..., p_n defines a subsimplex by
        // taking the vertices to be the barycenters of p_0,...,p_i for all i
        val n = simp.length - 1
        
        coveringSubSimps(simp).forall ({ subSimp =>
          val pointsCovered = subSimp.forall(p =>
            cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
          )
          if (! pointsCovered) {
            println(
            subSimp.find(p =>
              ! cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
            )
            )
          }
          pointsCovered && covers(cover, subSimp)
        })
      }
    }

    if (hasEmb.length == 0) {
      c <= 0
    } else {
      var i = 0
      val cover = hasEmb.filter(p => p.qsum > c)
        .map({ p =>
          val simp = project(p)
          i = i + 1
          println(i)
          (simp, leastSquaresMatrix(simp))
        })
      val n = hasEmb.head.length
      val simp = (0 until n).toVector
        .map(i => Vector.tabulate(n)({
          case `i` => c
          case _ => zero
        }))
      
      val partialSums = simp.scanLeft(Vector.fill(n)(zero))(addPoints).drop(1)
      val subSimp = (0 until n)
            .map(i => partialSums(i).map(_ / (i+1))).toVector
      //println(s"cover: ${cover.map(_._1)}\nsimp: $subSimp")
      //cover.map(_._1).foreach { println _ }
      //subSimp.foreach { println _ }
      println("starting.")
      covers(cover, subSimp)
    }
  }

  def lowerboundDouble(hasEmb: Vector[Vector[Rational]], c: Double) = {
    val tol: Double = 0.1**12
    // `p` implies a simplex in hyperplane sum x_i = c embeds.
    // returns vertices of this simplex
    def project(p: Vector[Rational]): Vector[Vector[Double]] = {
      (0 until p.length).toVector.map(i =>
        p.updated(i, p(i) - (1 - c)).map(_.toDouble)
      )
    }

    type Point = Vector[Double]
    type Simplex = Vector[Vector[Double]]
    type DMatrix = FieldMatrix[Double]
    // We want to solve A.x = b where
    // val b = RatMatrix(Vector(p :+ r"1")).transpose
    // val A = RatMatrix(simp).transpose.addConstantRows(1, r"1").
    // x = (A^t A)^-1 A^t b
    // x gives the least squares solution, i.e. minimises ||A.x - b||
    // `simpMat` is ((A^t A)^-1 A^t)^t.    
    def isPointInSimp(p: Point, simp: Simplex,
      simpMat: Option[DMatrix]): Boolean = {
      simpMat match {
        case None => {
          val b = FieldMatrix[Double](Vector(p :+ 1.0)).transpose
          val A = FieldMatrix[Double](simp).transpose.addConstantRows(1, 1.0)
          // Equation we want to solve is A.x = b
          // then we check all coordinates of x are in range [0,1].
          //println(s"Equation: A=$A\n b=$b")
          A.solveApprox(b, tol) match {
            case Left(_) => false
            case Right(x) => {
              //println(s"Coeffs: $x")
              x.transpose.mat(0).forall(coord => coord >= -tol && coord <= 1+tol)
            }
          }
        }
        case Some(x) => {
          val b_trans = FieldMatrix[Double](Vector(p :+ 1.0))
          //  (x * b).transpose.mat(0).forall(coord => coord >= 0 && coord <= 1)
          (b_trans * x).mat(0).forall(coord => coord >= 0 && coord <= 1)
        }
      }
    }

    // Computes matrix ((A^t A)^-1 A^t)^t (see `isPointInSimp` function)
    def leastSquaresMatrix(simp: Simplex): DMatrix = {
      val A = FieldMatrix[Double](simp).transpose.addConstantRows(1, 1.0)

      (A.transpose * A).inverseApprox(tol) match {
        case Right(x) => A * x.transpose //x * A.transpose
        case Left(x) => {
          throw new Exception(s"Non-invertible matrix. Simplex is degenerate: $x")
        }
      }
    }


    // is `simp1` contained in `simp2`?
    def isSimpInSimp(simp1: Simplex, simp2: Simplex,
      simp2Mat: Option[DMatrix] = None): Boolean = {
      // Check if all points of simp1 are in simp2
      simp1.forall(p => isPointInSimp(p, simp2, simp2Mat))
    }

    def addPoints(p1: Point, p2: Point): Point =
      (0 until p1.length).toVector.map(i => p1(i) + p2(i))

    def subtractPoints(p1: Point, p2: Point): Point =
          (0 until p1.length).toVector.map(i => p1(i) - p2(i))

    // Return subsimplices which cover `simp`
    def coveringSubSimps(simp: Simplex): Vector[Simplex] = {
      val n = simp.length - 1 // dimension of simplex
      val scale = 1.0*n/(n+1) // (dist vert to center)/(vert to ctr of opp face)
      simp.map({ origin =>
        simp.map(p => addPoints(subtractPoints(p, origin).map(_*scale), origin))
      })
    }

    // do the simplices in `cover` cover the entire simplex `simp`
    // `cover` also requires `leastSquaresMatrix` to be passed (speeds up computation).
    //@tailrec
    var calls = 0
    def covers(cover: Vector[(Simplex, DMatrix)], simp: Simplex): Boolean = {
      calls = calls + 1
      if (calls % 1000 == 0) {
        println(s"calls: $calls")
        //if (calls > 10000)
        //  sys.exit(1)
      }

      if (cover.exists({ case (s, mat) => isSimpInSimp(simp, s, Some(mat)) })) {
        true
      } else {
        // barycentric subdivide and recursively call
        // for n simplex this creates (n+1)! subsimplices
        // If v_0,..., v_n are the vertices of the simplex.
        // Then any permutation p_0, ..., p_n defines a subsimplex by
        // taking the vertices to be the barycenters of p_0,...,p_i for all i
        val n = simp.length - 1
        
        coveringSubSimps(simp).forall ({ subSimp =>
          val pointsCovered = subSimp.forall(p =>
            cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
          )
          if (! pointsCovered) {
            println(
            subSimp.find(p =>
              ! cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
            )
            )
          }
          pointsCovered && covers(cover, subSimp)
        })

        /*
        simp.permutations.forall({ perm =>
          val partialSums = perm.scanLeft(Vector.fill(n+1)(0.0))(addPoints).drop(1)
          val subSimp = (0 until n+1)
            .map(i => partialSums(i).map(_ / (i+1))).toVector
          //println(s"subSimp: $subSimp")
          // check if all vertices are covered
          val pointsCovered = subSimp.forall(p =>
            cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
          )
          if (! pointsCovered) {
            println(
            subSimp.find(p =>
              ! cover.exists({ case (s, mat) => isPointInSimp(p, s, Some(mat)) })
            )
            )
          }
          pointsCovered && covers(cover, subSimp)
        })*/
      }
    }

    if (hasEmb.length == 0) {
      c <= 0
    } else {
      val cover = hasEmb.filter(p => p.qsum > c)
        .map({ p =>
          val simp = project(p)
          (simp, leastSquaresMatrix(simp))
        })
      val n = hasEmb.head.length
      val simp = (0 until n).toVector
        .map(i => Vector.tabulate(n)({
          case `i` => c
          case _ => 0.0
        }))
      
      val partialSums = simp.scanLeft(Vector.fill(n)(0.0))(addPoints).drop(1)
      val subSimp = (0 until n)
            .map(i => partialSums(i).map(_ / (i+1))).toVector
      //println(s"cover: ${cover.map(_._1)}\nsimp: $subSimp")
      //cover.map(_._1).foreach { println _ }
      //subSimp.foreach { println _ }
      covers(cover, subSimp)
    }
  }

}
