
package ahmad.hfhomology
import spire.implicits._
import spire.math._
import java.io.File
import java.io.PrintWriter

/**
  * @param embPts - points in Q^3 with embeddings.
  * @param nonEmbPts - points in Q^3 without embeddings.
  * @param codims - codim[i] is min codim of embedding for embPts[i].
  */
case class TriangleData(embPts: Vector[RatPoint],
  nonEmbPts: Vector[RatPoint],
  codims: Vector[Int]) {
  def withPermutations: TriangleData = {
    def withPerms(pts: Vector[RatPoint]) = {
      pts.flatMap({ case (p1, p2, p3) =>
        Vector(p1, p2, p3).permutations.toVector.distinct.map(vec =>
          (vec(0), vec(1), vec(2)))
      })
    }

    val nonEmbPtsPermed = withPerms(nonEmbPts).distinct
    val embPtsCodims = embPts.zip(codims).flatMap({ case (pt, codim) =>
      val (p1, p2, p3) = pt
      Vector(p1, p2, p3).permutations.toVector.distinct.map(vec =>
          ((vec(0), vec(1), vec(2)), codim))
    })
    val (embPtsPermed, codimsPermed) = embPtsCodims.distinct.unzip
    TriangleData(embPtsPermed, withPerms(nonEmbPts).distinct, codimsPermed)
    //TriangleData(withPerms(embPts).distinct, withPerms(nonEmbPts).distinct, codims)
  }
}

object TriangleData {
  /** Convert rational point of SFS(1; pt) to point on triangle in R^2.
    */
  def toXY(pt: RatPoint): (Double, Double) = {
    val (x, y, z) = pt
    val c = 1/x + 1/y + 1/z
    ((1/z - 1/x + c).toDouble/math.sqrt(2), math.sqrt(3.0/2.0)*(1/y).toDouble)
  }

  // Converts from R^2 of triangle projection of tetrahedron face
  // to SFS(1; pts) 
  def fromXY(x_r2: Double, y_r2: Double): (Double, Double, Double) = {
    // Want (x, y, z) with 1/x + 1/y + 1/z = 1 and toXY((x,y,z)) = (x_r2, y_r2)
    val y = math.sqrt(3.0/2.0) / y_r2
    val z = 2.0 / (math.sqrt(2.0)*x_r2 - math.sqrt(2.0/3.0)*y_r2)
    val x = 1.0 / (1.0 - 1.0/y - 1.0/z)
    (x, y, z)
  }

  def loadFromFiles(filenameEmbPts: String, filenameNonEmbPts: String): TriangleData = {
    import scala.io.Source
    val nonEmbPts = Source.fromFile(filenameNonEmbPts)
      .getLines()
      .toVector
      .map(line => line.split(",").map(Rational(_)))
      .map(vec => (vec(0), vec(1), vec(2)))

    val embPts = Source.fromFile(filenameEmbPts)
      .getLines()
      .toVector
      .map(line => line.split(",").map(Rational(_)))
      .map(vec => (vec(0), vec(1), vec(2)))

    val codims = Source.fromFile(filenameEmbPts)
      .getLines()
      .toVector
      .map(line => line.split(","))
      .map(vec => vec(3).toInt)

    TriangleData(embPts, nonEmbPts, codims).withPermutations
  }

  /*
  def loadFromFiles(filenameEmbPts: String, filenameNonEmbPts: String): TriangleData = {
    import scala.io.Source
    val combinedPts = 
    for (filename <- Vector(filenameEmbPts, filenameNonEmbPts)) yield {
      Source.fromFile(filename)
        .getLines()
        .toVector
        .map(line => line.split(",").map(Rational(_)))
        .map(vec => (vec(0), vec(1), vec(2)))
    }
    TriangleData(combinedPts(0), combinedPts(1)).withPermutations
  }*/

  def generate(
    knownEmbs: Vector[((Rational, Rational, Rational), Int)]=Vector(), // codims needed
    knownNonEmbs: Vector[(Rational, Rational, Rational)]=Vector(),
    skipped: Vector[(Rational, Rational, Rational)]=Vector()
  ) = {

    println(s"Already known non-emb points: ${knownNonEmbs.length}")
    var hasLatticeEmb = Vector[(Rational, Rational, Rational)]()
    var noLatticeEmb = Vector[(Rational, Rational, Rational)]()
    
    val upper = 170
    val hasEmbWriter = new PrintWriter(new File("3fib_170_has_emb.txt"))
    val noEmbWriter = new PrintWriter(new File("3fib_170_no_emb.txt"))
    val skippedWriter = new PrintWriter(new File("3fib_170_skipped.txt"))

    for (
       a1 <- 2 to upper; b1 <- 1 until a1 if gcd(a1,b1) == 1 
      ;a2 <- 2 to upper; b2 <- 1 until a2 if gcd(a2,b2) == 1 && a1*b2 <= a2*b1

    ) {
      //val a2 = a1
      //val b2 = b1
      val r1 = Rational(a1, b1)
      val r2 = Rational(a2, b2)

      if (1 - 1/r1 - 1/r2  > 0) {
        val r3 = 1/(1 - 1/r1 - 1/r2)
        //if (r4.numerator <= upper && r4 >= r3)
        if (r3.numerator <= upper && r3 >= r2)
        {
          //if (r3.numerator < 12 || (1/r3 < 0.9 && 1/r3 > 0.1)) {
          //val sfs = SFSOverS2(-1,Vector(-r1, -r2, -r3, -r4))
          val sfs = SFSOverS2(-1,Vector(-r1, -r2, -r3))

          if (knownNonEmbs.contains((r1,r2,r3))) { // already computed
            //println(s"Already computed (no emb): ${(r1,r2,r3)}")
            //sys.exit(0)
            val perms = Vector((r1,r2,r3), (r1,r3,r2), (r2,r1,r3), (r2,r3,r1),
              (r3,r1,r2), (r3,r2,r1))
            noEmbWriter.write(s"$r1,$r2,$r3\r\n")
            noEmbWriter.flush()

            noLatticeEmb = perms ++ noLatticeEmb
            
          } else if (knownEmbs.exists(x => x._1 == (r1,r2,r3))) {
            //println(s"Already computed (has emb): ${(r1,r2,r3)}")
            val codim = knownEmbs.find(x => x._1 == (r1,r2,r3)).get._2
            val perms = Vector((r1,r2,r3), (r1,r3,r2), (r2,r1,r3), (r2,r3,r1),
                  (r3,r1,r2), (r3,r2,r1))
            hasLatticeEmb = perms ++ hasLatticeEmb
            hasEmbWriter.write(s"$r1,$r2,$r3,$codim\r\n")
            hasEmbWriter.flush()
          } else if (skipped.contains((r1,r2,r3))) {
            println(s"SKIPPED: $sfs")
            skippedWriter.write(s"$r1,$r2,$r3\r\n")
            skippedWriter.flush()
          } else {
            println(s"trying: ${(r1,r2,r3)}")
            sfs.toTree.toIntersectionForm.embeddingsMaxDuration(25000) match {
              //val time = System.currentTimeMillis()
              //Some(sfs.toTree.toIntersectionForm.embeddings()) match {
              case Some(embs) => {
                val hasEmb = ! embs.isEmpty
                println(s"$sfs has embeddings: $hasEmb")
                //assert(System.currentTimeMillis() - time < 30000)
                val perms = Vector((r1,r2,r3), (r1,r3,r2), (r2,r1,r3), (r2,r3,r1),
                  (r3,r1,r2), (r3,r2,r1))

                if (hasEmb) hasLatticeEmb = perms ++ hasLatticeEmb
                if (hasEmb) {
                  //hasEmbWriter.write(s"{$r1,$r2,$r3,$r4},")
                  val codim = LatticeEmbedding.codimOfEmb(embs(0))
                  hasEmbWriter.write(s"$r1,$r2,$r3,$codim\r\n")
                  hasEmbWriter.flush()
                } else {
                  //noEmbWriter.write(s"{$r1,$r2,$r3,$r4},")
                  noEmbWriter.write(s"$r1,$r2,$r3\r\n")
                  noEmbWriter.flush()
                  //println((1/r1 + 1/r2 + 1/r3).toDouble)
                  noLatticeEmb = perms ++ noLatticeEmb
                }

              }
              case _ => {
                println(s"SKIPPED: $sfs")
                skippedWriter.write(s"$r1,$r2,$r3\r\n")
                skippedWriter.flush()
              }

            }
          }
        }
      }
    }

    hasEmbWriter.close()
    noEmbWriter.close()
    skippedWriter.close()
  }
}

