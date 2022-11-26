 
package ahmad.hfhomology

import spire.implicits._
import spire.math._

case class AmphicheiralSymmetry(q: Matrix, emb1: Matrix, emb2: Matrix) {

  /*
   spincs = {{{-17615}, {1}, {0}, {1258}, {6665}, {6682}},
  {{-33155}, {1}, {0}, {2368}, {12545}, {12576}},
  {{-48695}, {1}, {0}, {3478}, {18425}, {18470}},
  {{-64235}, {1}, {0}, {4588}, {24305}, {24364}},
  {{-79775}, {1}, {0}, {5698}, {30185}, {30258}},
  {{-60091}, {1}, {0}, {4292}, {22737}, {22790}},
  {{-75631}, {1}, {0}, {5402}, {28617}, {28684}},
  {{-91171}, {1}, {0}, {6512}, {34497}, {34578}},
  {{-106711}, {1}, {0}, {7622}, {40377}, {40472}},
  {{-122251}, {1}, {0}, {8732}, {46257}, {46366}},
  {{-137791}, {1}, {0}, {9842}, {52137}, {52260}},
  {{-153331}, {1}, {0}, {10952}, {58017}, {58154}},
  {{-168871}, {1}, {0}, {12062}, {63897}, {64048}},
  {{-149187}, {1}, {0}, {10656}, {56449}, {56580}},
  {{-164727}, {1}, {0}, {11766}, {62329}, {62474}},
  {{-180267}, {1}, {0}, {12876}, {68209}, {68368}},
  {{-195807}, {1}, {0}, {13986}, {74089}, {74262}}}

   Table[s = spincs[[i]]; 
  w = {{-3, 1, 0, 0, 1, 1}, {1, -3, 1, 0, 0, 0}, {0, 1, -4, 2, 0, 
     0}, {0, 0, 2, -4, 1, 0}, {1, 0, 0, 1, -3, 0}, {1, 0, 0, 0, 
     0, -2}};
  (s - 2 * 
       w.{{Round[a1]}, {Round[a2]}, {Round[a3]}, {Round[a4]}, {Round[
           a5]}, {Round[a6]}}  /. 
     NMinimize[
       Norm[s - 2 * w.{{a1}, {a2}, {a3}, {a4}, {a5}, {a6}} ], {a1, a2,
         a3, a4, a5, a6}, Reals][[2]] ) // MatrixForm, {i, 1, 
   17}]  // TeXForm

   */

  // Spin^c(Y), Y = dbc(K), K = strongly negative amphicheiral
  // Spin^c(Y) = Spin^c(X) / 2q, where X has intersection form q, X = dbc of checkerboard surface
  // q negative definite
  // L Spin^c(Y) = (u mod 2) / 2D, where D = L q R is smith form for some u (see spincYInfo func below).

  // returns (u, D, L)
  val (u, d, left) = spincYInfo
  val leftInv = left.inverse

  def spincYInfo: (Matrix, Matrix, Matrix) = {
    val n = q.nRows

    // spinc(X) = { (diagonal entries of q) mod 2 } in dual basis of dual lattice
    // column vector
    val diag = Matrix(Vector((0 until n).toVector.map(i => (-q(i)(i)) % 2 ))).transpose

    // D = L q R be the smith normal form
    val (d, left, right) = q.extendedSmithForm
    assert(d == left * q * right)

    /* L spinc(Y) = L (diag mod 2) / 2 im D   (im LQ = im LQR = im D)
     anything in diag mod 2 is 2v + diag
     L (2v + diag) = 2Lv + L diag = L diag (mod 2)
    */
    val u = left * diag // L spinc(Y) = (u mod 2) / 2D

    // make entries positive
    val uPos = Matrix(Vector(
      (0 until u.nRows).toVector.map({ i =>
        val x = u(i)(0)
        val m = 2*d(i)(i)
        ((x % m) + m) % 2
      })
    )).transpose

    (uPos, d, left)
  }

  def spincYToOldBasis(s: Matrix) = {
    /* Converts s in L spin^c(Y) (good basis) to old basis. */
    leftInv * s
  }

  // Good basis L spincY
  def allSpincY = {
    sequence((0 until u.nRows).toVector
      .map(i => (u(i)(0).toInt until 2*d(i)(i).toInt by 2).toVector))
      .map(s => Matrix(Vector(s)).transpose)
  }

  // Orbit of a spincy under rho
  def orbit(s: Matrix) = {
    def loop(currS: Matrix, encountered: Set[Matrix]): Set[Matrix] = {
      if (encountered.contains(currS)) encountered
      else loop(rho(currS), encountered + currS)
    }
    loop(s, Set[Matrix]())
  }

  def orbits = {
    allSpincY.map(s => orbit(s)).distinct
  }

  /*  X_1 (=X) and X_2 are dbc of two dual checkerboard surfaces
      Assume both neg definite (after sign changes),
      Z = X_1 \cup X_2 has standard negative definite lattice
      Get restrictions r_i = Spinc(Z) -> spinc(X_i).
      emb_i is the lattice embedding H_2(X_i) -> H_2(Z) where vertices map to rows
      vertex for row j of emb_1 should get mapped to vertex for row j by the amphicheiral symmetry
   */
  def rho(s: Matrix) = {
    // s in L spinc(Y) (L changes basis)

    // spinc(Z) = { (odd entries) mod 2 } in e_i* dual basis
    normalizeSpincY(left * emb2 * pullback(leftInv * s, emb1))
  }



  // Have: spinc(Z) -> spinc(X) -> spinc(Y).
  // Given s in spinc(Y) computes an element in spin(Z) which maps to it. s is given in ORIGINAL BASIS not nice basis
  def pullback(s: Matrix, emb1: Matrix) = {

    /* Want sz in spinc(Z) with emb1 sz = s, emb1 is the adjoint of the map H_2(X)into H_2(Z).
       General element sz = 2v + (ones)         (ones = (1,1,...,1), v arbitrary)
       Write Dv = Lv emb1 Rv  (smith normal form), D will has ones on the diagonal (and some extra 0 columns) since emb1 surjects
       emb1 sz = s
       Lv^-1 Dv Rv^-1 (2v + ones) = s
       Dv Rv^-1 (2v + ones) = Lv * s
       Dv * Rv^-1 * v = 1/2 (Lv * s - Dv Rv^-1 ones)
       Dv * Dv^T = identity matrix since rows of D are orthonormal
       Take v = Rv Dv^T * 1/2(Lv * s - Dv Rv^-1 ones)
     */

    val (dv, lv, rv) = emb1.extendedSmithForm
    //println(s"dv: $dv")
    //println(s"lv: $lv")
    val ones = Matrix(Vector(Vector.fill(emb1.nCols)(1))).transpose
    val v = (rv * dv.transpose * (lv * s - dv * rv.inverse * ones)).map(entry => entry/2)
    val res = v*2 + ones
    res
  }

  // Puts the spinc structure into normal form
  // spinc is column vector (as matrix)
  def normalizeSpincY(spinc: Matrix) = {
    Matrix(Vector(
      (0 until spinc.nRows).toVector.map({ i =>
        val x = spinc(i)(0)
        val m = 2*d(i)(i)
        ((x % m) + m) % m
      })
    )).transpose
  }

  def spincYExtending(emb: Matrix) = {
    allSpincY.filter(s => extendsOverQHB(s, emb))
  }

  // s in L spinc nice basis
  def isRhoInvariant(ss: Vector[Matrix]) = ss.flatMap(s => orbit(s)).distinct.length == ss.length

  // s in L spinc(Y) (nice basis)
  // emb is embedding matrix of H_2(X) -> H_2(X \cup B), B = QHB
  def extendsOverQHB(s: Matrix, emb: Matrix) = {
    val ones = Matrix(Vector(Vector.fill(s.nRows)(1))).transpose
    // Solve 2 emb v = L^-1 s - emb * ones (mod 2d)
    
    (emb*2).toRatMatrix.solve((leftInv * s - emb * ones).toRatMatrix) match {
      case Left(s) => false
      case Right(v) => {
        // Need to check that denominator of v(i) is coprime to d(i)(i)
        (0 until s.nRows).forall(i => gcd(v(i)(0).denominator, d(i)(i)) == 1)
      }
    }
  }

}
