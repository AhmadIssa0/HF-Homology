 
package ahmad.hfhomology

import spire.implicits._
import spire.math._

object NonEqSliceSNAK {

  def main(args: Array[String]): Unit = {
    // The knot 12a_1105 is a non-equivariantly slice SNAK.

    // emb11 and emb22 are the J_{+/-} in our paper.
    val emb11 = Matrix( // 12a_1105
     Vector(Vector(1,0,0,0,-1,1,0,0,0,0,0,0),
     Vector(-1,1,0,0,0,0,0,1,0,0,0,0),
     Vector(0,-1,1,0,0,0,0,0,1,0,0,1),
     Vector(0,0,-1,1,0,0,0,0,0,1,0,-1),
     Vector(0,0,0,-1,1,0,0,0,0,0,1,0),
     Vector(0,0,0,0,0,-1,1,0,0,0,0,0)))

    val emb22 = Matrix( // 12a_1105
     Vector(Vector(0,0,0,0,0,0,0,0,-1,1,0,1),
     Vector(0,1,0,0,0,0,0,-1,1,0,0,0),
     Vector(1,0,0,0,0,-1,-1,1,0,0,0,0),
     Vector(0,0,0,0,1,1,1,0,0,0,-1,0),
     Vector(0,0,0,1,0,0,0,0,0,-1,1,0),
       Vector(0,0,1,0,0,0,0,0,0,0,0,-1)))

    // Print these things as basic checks.
    println(s"int? ${emb11 * emb11.transpose}")
    println(s"int? ${emb22 * emb22.transpose}")
    println((emb22 * emb22.transpose).invariantFactors)

    // The intersection form. Our code is written to deal with negative
    // definite forms for Donaldson's theorem so we have a minus.
    val qint = IntersectionForm((emb11 * emb11.transpose * -1).toIntVector)

    // Create the object which deals with the symmetry.
    val as = AmphicheiralSymmetry(qint.toMatrix, emb11, emb22)

    // Print out our matrices for good measure.
    println(s"emb11 = ${emb11}")
    println(s"emb22 = ${emb22}")


    println(s"u = ${as.u}")
    println(s"d = ${as.d}")
    as.orbits.foreach { println }
    //val spincy = Matrix(Vector(Vector(1,0,0,0,2))).transpose
    //println(as.rho(Matrix(Vector(Vector(1,0,0,18,10))).transpose))

    
    //println(as.normalizeSpincY(as.left * emb11 * as.pullback(as.leftInv * spincy, emb11)))
    //println(s"pullback: ${as.pullback(as.leftInv * spincy, emb11)}")

    """
    IntersectionForm(Vector(
      Vector(-5,1,1,1,1),
      Vector(1,-3,1,0,0),
      Vector(1,1,-3,1,0),
      Vector(1,0,1,-3,1),
      Vector(1,0,0,1,-3)))
    """
    println(qint.det)
    val embsm = qint.embeddingsAsMatrices(Some(qint.rank))
    println(s"${embsm.length} lattice embeddings")
    embsm.foreach { println }


    println(s"Good basis is in L Spin^c(Y). L = ${as.left}")
    println("spinc which extend")
    as.spincYExtending(embsm(0)).foreach { println }
    println("spinc which extend (old basis)")
    as.spincYExtending(embsm(0)).foreach { s => println(as.spincYToOldBasis(s)) }
    for (i <- 0 until embsm.length) {
      println(s"Spinc rho eq? ${as.isRhoInvariant(as.spincYExtending(embsm(i)))}")
    }
    println(s"q = ${as.q}")
    val secondvec = Matrix(Vector(Vector(3, -3, 2, 0, -1, -2))).transpose
    println(s"Pullback of 2nd vector: ${as.pullback(secondvec, emb11)}")
    sys.exit(0)
  }


}
