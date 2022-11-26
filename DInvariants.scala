
package ahmad.hfhomology

import spire.math._
import spire.algebra.Monoid
import spire.implicits._

object DInvariants {
  def possibleAlexPoly(dInvs: Vector[Rational], r: Rational): Vector[Vector[SafeLong]] = {
    if (r < 0) possibleAlexPoly(dInvs.map(-_), -r)
    else {
      val h1 = dInvs.length
      def reorder(a: Int, c: Int) = {
        (0 until h1).toVector.map(i => dInvs((a*i + c) % h1))
      }
      val (p, q) = (r.numerator.toInt.abs, r.denominator.toInt.abs)
      val lens = LensSpace.dInvariants(p, q)
  
      (1 to h1).toVector.filter(a => gcd(a, h1) == 1).flatMap({ a =>
        (0 until h1).toVector.flatMap(c => alexPoly(reorder(a, c), r, lens) match {
          case None => Vector()
          case Some(v) => Vector(v)
        })
      }).distinct
    }
  }

  // lensInvs should equal LensSpace.dInvariants(p, q) where p/q = |r|.
  // Allowed to pass it in to speed up the computation (avoids recomputing).
  def alexPoly(dInvs: Vector[Rational],
    r: Rational,
    lens: Vector[Rational]
  ): Option[Vector[SafeLong]] = {
    require(r != 0)
    if (r < 0) alexPoly(dInvs.map(r => -r), -r, lens)
    else {
      val (p, q) = (r.numerator.toInt, r.denominator.toInt)
      // LensSpace.dInvariants returns d-inv for p/q surgery on unknot
      //val lens = LensSpace.dInvariants(p, q)
      //println("lens: " + lens)
      //println("dInvs: " + dInvs)
      // For -p/2 <= i <= p/2,
      // computes d(S^3_{p/q}(K), i) - d(S^3_{p/q}(U), i).
      // if i outside this range return 0
      def diff(i: Int): Rational = {
        if (i < Rational(-p,2) || i > Rational(p, 2)) 0
        else {
          val j = i + Rational(p, 2).floor.toInt
          //require(j < dInvs.length, s"p=$p")
          dInvs(j % p) - lens((i + p) % p)
        }
      }


      lazy val satisfiesSymmetry =
        (Rational(-p,2).ceil.toInt to Rational(p,2).floor.toInt)
          .groupBy(i => Rational(i, q).floor.abs)
          .toVector
          .map(_._2)
          .forall { v => v.forall(i => diff(i) == diff(v(0))) }

      lazy val bottomTorsionIsZero = {
        val i = Rational(-p,2).ceil
        if (i.abs > Rational(p, 2*q)) diff(i.toInt) == 0
        else true
      }

      //println("Grouped: " + (Rational(-p,2).ceil.toInt to Rational(p,2).floor.toInt)
      //  .groupBy(i => Rational(i, q).floor.abs))
      //println(s"diff(0) = ${diff(0)}, diff(1) == ${diff(1)}, diff(-1) == ${diff(-1)}")

      val diffAreWhole =
        (Rational(-p,2).ceil.toInt until Rational(p,2).floor.toInt)
          .forall { i => diff(i).isWhole && diff(i).toSafeLong % 2 == 0 }

      if (!diffAreWhole || !satisfiesSymmetry || !bottomTorsionIsZero) None
      else {
      // alexTail = Vector(a_1, ..., a_n) coefficients of symmetrized polynomial
      val alexTail = (1 to Rational(p,2*q).ceil.toInt).toVector.map(i =>
        (diff((i+1)*q.toInt) - 2*diff(i*q.toInt) + diff(q.toInt*(i-1)))/(-2)
      )

      //println("alexTail: " + alexTail)
  
         
      /*
      (Rational(-p,2).ceil.toInt until Rational(p,2).floor.toInt).forall { i =>
        if (Rational(i, q).floor.abs  == Rational(i+1, q).floor.abs) {
          //println("i="+i + " " + diff(i) + " " + diff(i+1))
          diff(i).isWhole() && diff(i) == diff(i+1)
        } else diff(i).isWhole()
      }*/

      // 3-genus as largest power in Alexander polynomial
      val genus = alexTail.reverse.dropWhile(_ == 0).length

      val alexTrailing0s = (1 - 2*alexTail.qsum) +: alexTail
      val alex = alexTrailing0s.reverse.dropWhile(_ == 0).reverse
      val alexNoZeros = alex.filter(_ != 0)

      val torsion = (0 to Rational(p, 2*q).floor.toInt).toVector.map { i =>
        sum(1, alex.length-i-1)(j => j*alex(i + j))
      }
      //println("BEGIN")
      val agreesWithAbsGr = (0 to Rational(p, 2).floor.toInt).forall { i =>
        //println("i=" + i)
        //println(s"Agree: ${diff(i)} and ${-2*torsion(Rational(i, q).floor.toInt)}") 
        diff(i) == -2*torsion(Rational(i, q).floor.toInt)
      }
      //println("END")

      /** The symmetrized alexander polynomial satisfies A(1) = 1.
        * Thus, a_0 + 2 * sum_{i>0} a_i = 1.
        * So a_0 = 1 - 2 * sum_{i>0} a_i.
        */
      if (agreesWithAbsGr && satisfiesSymmetry && r >= 2*genus - 1) {
        if (alex.forall(a => a == 0 || a == 1 || a == -1) &&
            (0 until alexNoZeros.length - 1).forall(i =>
              alexNoZeros(i) == -alexNoZeros(i+1))) {
          //println("Torsion: " + torsion)
          //println("Dinvs: " + dInvs)
          //println("Lens: " + lens)
          //println("Alex: " + alex)
          //(0 until 2).foreach { i => println(s"${diff(i)}, ${diff(-i)}") }
          Some(alex.map(_.toSafeLong))
        } else
          None
      } else None
      }

    } 
  }

  /**  Let M be the SFS over S^2 given by the negative definite plumbing
    *  with central weight e_0 < 0 and weights on legs corresponding
    *  to the rationals:
    *        -alpha_i/omega_i < 0 for 1 <= i <= v.
    * 
    *  We reference the following paper by Nemethi (journal copy):
    *   On the Ozsvath-Szabo invariant of negative definite plumbed 3-manifolds
    * 
    *  Let k be a characteristic element in H_2(X, M) = H^2(X).
    *  d(M, [k]) = ((k_r)^2 + s)/4 - 2 min_{i >= 0} tau(i),
    *  where s is the number of vertices in the plumbing graph
    *        (k_r)^2 + s = K^2 + s - 8 \Chi(l'_[k])         [Section 11.9].
    * 
    *  @param coeffs is Vector(alpha_1/omega_1, ..., alpha_v/omega_v).
    * 
    *  @return Pairs of (s, d-inv) where spinc is given by SI_red in Prop 11.5,
    *          and d-inv is the corresponding d-inv d(M, s).
    *          Note that M is oriented as boundary of negative definite plumbing.
    */
  type Spinc = Vector[SafeLong] // Spinc Vector(a_0, ..., a_v) as in SI_red of Prop 11.5.
  type SpincHomClass = Vector[SafeLong]
  type Homology = Vector[SafeLong] // Vector(n1, n2,...) is Z/n1 + Z/n2 + ...
  type DInvariant = Rational
  case class DInvs(homology: Homology, dInvs: Vector[(DInvariant, SpincHomClass)]) {
    def reverseOrientation = DInvs(homology, dInvs.map {case (d, s) => (-d, s)})
    def raw: Vector[DInvariant] = dInvs.map(_._1)
  }
  def sfs(e_0: SafeLong, coeffs: Vector[Rational]): DInvs = {
    val v = coeffs.length
    val alpha = coeffs.map(_.numerator)
    val omega = coeffs.map(_.denominator)

    // e is the generalised orbifold number, e < 0 since assuming negative definite
    val e: Rational = e_0 + coeffs.map(r => 1/r).qsum
    require(e < 0, "SFS must bound a negative definite plumbing.")
    require(coeffs.forall(c => c > 1), s"Coefficients must be greater than 1, given: $coeffs")
    // ep = (2 - v + sum_l (1/alpha_l))/e   "log discrepency of central vertex"
    val ep = (Rational(2) - v + sum(0, v-1)(i => Rational(1,alpha(i)))) / e
    
    /**  The spin^c structures on M are in bijection with the set of integers
      *  (a_0, a_1, ..., a_v) satisfying:
      *  1) 0 <= a_0, and
      *  2) 0 <= a_i < alpha_i for 1 <= i <= v, and
      *  3) 1 + a_0 + i*e_0 + sum_j(floor((i*omega_j + a_j)/alpha_j)) <= 0 for all i > 0.
      *  This is (SI_red) in Proposition 11.5.
      */
    
    /**  Claim: Given (a_0, ..., a_v) satisfying (1) and (2), condition (3) holds provided
      *  it holds for 0 < i <= ceil((1 + a_0 + v)/|e|). In particular, since a_0 <= -e_0 from
      *  (3), we only need to check 0 < i <= ceil((1 - e_0 + v)/|e|).
      * 
      *  Proof:
      *  Let S = 1 + a_0 + i*e_0 + sum_j floor((i*omega_j + a_j)/alpha_j) (LHS of (3)).
      *  S <= 1 + a_0 + i*e_0 + sum_j (i*omega_j + alpha_j)/alpha_j
      *     = 1 + a_0 + v + i*e.
      *  Thus, S <= 0 provided 
      *    1 + a_0 + v + i*e <= 0, or equivalently
      *    (1 + a_0 + v)/(-e) <= i.
      *  Thus (3) holds provided S <= 0 for 0 < i <= ceil((1 + a_0 + v)/|e|), as required.
      */

    /**  Thus, given (a_1, ..., a_v) satisfying (2). 
      *  All 0 <= a_0 <= min -(1 + i*e_0 + sum_j floor((i*omega_j + a_j)/alpha_j))
      *  will satisfy (3).
      */

    // For as = Vector(a_1, ..., a_v), compute maximum value for a_0 satisfying (3).
    def a0Max(as: Vector[SafeLong]) = {
      def upperbound(i: SafeLong) = {
        val bd = 
          -(Rational(1) + i*e_0 +
            sum(0, v-1)(j => Rational(i*omega(j) + as(j), alpha(j)).floor))
          
        bd.floor.toSafeLong
      }

      var a0Max = upperbound(1)
      var i = 2
      while (i <= (Rational(max(SafeLong(0), a0Max) + v + 1)/Rational(-e)).ceil.toSafeLong &&
             a0Max >= 0) {
        a0Max = min(upperbound(i), a0Max)
        i += 1
      }
      a0Max
    }

    def sequence[A](v: Vector[Vector[A]]): Vector[Vector[A]] = v match {
      case Vector() => Vector(Vector())
      case x +: xs => x.flatMap(e => sequence(xs).map(e +: _))
    }

    val allSpinc: Vector[Spinc] = {
      val aTail = sequence(alpha.map(alpha_i =>
        (0 until alpha_i.toInt).map(SafeLong(_)).toVector))
      aTail.flatMap(a => Interval.closed(SafeLong(0), a0Max(a)).iterator(1).map(a0 => a0 +: a))
    }

    /** From end of Section 11.8:
      * -Chi(-l'_[k]) = sum_{l=0}^v (a_l /2) + ep * aTilde / 2 + aTilde^2 / (2e) 
      *                 - sum_{l=1}^v [sum_{j=1}^{a_l} frac(j*omega'_l / alpha_l))]
      *  where
      *        omega'_l * omega_l = 1 (mod alpha_l), with 0 < omega'_l < alpha_l,
      *        [k] = (a_0, ..., a_v) is a spinc structure,
      *        aTilde = a_0 + sum_{l} (a_l / alpha_l),
      *        ep = (2 - v + sum_l (1/alpha_l))/e   "log discrepency of central vertex"
      */
    def negChi(a: Spinc): Rational = {
      val aTilde = Rational(a(0)) + (0 until v).map(i => Rational(a(i + 1), alpha(i))).qsum
      val omegaP = (0 until v).map(i => omega(i).toBigInt.modInverse(alpha(i).toBigInt).toSafeLong)
      val c = (0 to v).map(i => Rational(a(i), 2)).qsum + ep*aTilde/2 + (aTilde ** 2)/(2*e)
      val d = (0 until v).map(i =>
          Interval.closed(SafeLong(1), a(i + 1)).iterator(1).map({ j =>
            val x = Rational(j*omegaP(i), alpha(i))
            x - x.floor
          }).toVector.qsum
        ).qsum
      c - d
    }

    /** Section 11.9:
    * Ks := K^2 + s = ep^2 * e + e + 5 - 12 * sum_{i=1}^v s(omega_l, alpha_l)
    * where for 0 < p, q relatively prime,
    *       s(p, q) = sum_{i=1}^q ((i/q)) ((pi/q)) is the Dedekind sum function
    *                 where ((x)) = 0 for x integral,
    *                               x - floor(x) - 1/2 otherwise. 
    */

    // sawtooth(x) = ((x))
    def sawtooth(x: Rational): Rational =
      if (x.isWhole()) 0
      else (x - x.floor - r"1/2")

    def s(p: SafeLong, q: SafeLong): Rational =
      sum(SafeLong(1), q)(i =>
        sawtooth(Rational(i,q)) * sawtooth(Rational(i*p, q))
      )

     // K^2 + s
    val Ks: Rational =
      (ep**2)*e + e + 5 - 12 * (0 until v).map(i => s(omega(i), alpha(i))).qsum


    /**  Fix a spinc structure (a_0, ..., a_v).
      *  Let delta(t) = 1 + a_0 - t*e_0 + sum_{j=1}^v floor((-t*omega_j + a_j)/alpha_j), t >= 0.
      *  Let tau(0) = 0, and
      *      tau(i) = sum_{t=0}^{i-1} delta(t) for i > 0.
      * 
      *  Claim: tau(i) is minimised for some 0 <= i <= ceil((v - a_0 - 1)/(-e)).
      * 
      *  Proof: It suffices to show that delta(t) >= 0 for t > ceil((v - a_0 - 1)/(-e)).
      *  We have,
      *    delta(t) >= 1 + a_0 - t*e_0 + sum_{j=1}^v ((-t*omega_j + a_j)/alpha_j - 1)
      *             >= 1 + a_0 - t(e_0 + sum_{j=1}^v omega_j/alpha_j) - v
      *              = 1 + a_0 - t*e - v
      *  Hence, delta(t) >= 0 provided that
      *    1 + a_0 - t*e - v >= 0, or equivalently
      *    t >= (v - a_0 - 1)/(-e), as required. 
      */
    def minTau(a: Spinc): Rational = {
      def delta(t: SafeLong) = r"1" + a(0) - e_0*t + (0 until v).map(j =>
        Rational(-t*omega(j) + a(j + 1), alpha(j)).floor).qsum
      val upper = (Rational(v - a(0) - 1) / (-e)).ceil.toSafeLong

      // tauPrev = tau(i)
      def loop(tauMin: Rational = 0, tauPrev: Rational = 0, i: SafeLong = 0): Rational = {
        if (i > upper) tauMin
        else {
          val d = delta(i)
          loop(min(tauMin, tauPrev + d), tauPrev + d, i + 1)
        }
      }
      loop()
    }

    val (hom, spinAsHom) = spincAsHomologyClass(e_0, coeffs, allSpinc)
    val dInvs = for (a <- allSpinc) yield {
      (Ks + 8*negChi(a))/4 - 2*minTau(a)
    }
    DInvs(hom, dInvs.toVector.zip(spinAsHom).sortWith((a, b) => a._2 < b._2))
  }

  /**  Expresses r = p/q > 1 as
    *    p/q = a_0 - 1/(a_1 - 1/(a_2 - ... 1/a_n)),
    *  where a_i >= 2 for all i.
    *  @return Vector(a_0, a_1, ..., a_n)
    */
  def toContinuedFraction(r: Rational): Vector[SafeLong] = {
    require(r > 1)
    val (p, q) = (r.numerator, r.denominator)
    if (q == 1) Vector(p)
    else {
      val a: SafeLong = p/q + 1 // add 1 so 5/4 = 2 - ...
      // p/q = a - 1/r
      // r = q/(aq - p)     
      a +: toContinuedFraction(Rational(q, a*q - p))
    }
  }


  def fromContinuedFraction(contFrac: Vector[SafeLong]): Rational = contFrac match {
    case Vector() => throw new IllegalArgumentException()
    case Vector(a) => Rational(a)
    case a +: rest => a - 1/fromContinuedFraction(rest)
  }

  implicit val ratMonoid = new Monoid[Rational] {
    def id = 0
    def op(x: Rational, y: Rational) = x + y
  }

  implicit val safeLongMonoid = new Monoid[SafeLong] {
    def id = 0
    def op(x: SafeLong, y: SafeLong) = x + y
  }

  // sum_{i=a}^b f(i)
  def sum[A: Monoid, B: Integral](a: B, b: B)(f: B => A): A = {
    def loop(a: B, b: B, total: A): A = {
      if (a > b) total
      else loop(a + 1, b, Monoid[A].op(total, f(a)))
    }
    loop(a, b, Monoid[A].id)
  }

  /**  Converts a spinc structure given (as returned by DInvariants.sfs)
    *  by (a_0, ..., a_v) which satisfy SI_red in Proposition 11.5, and converts
    *  them into elements (h_1, ..., h_k) in Z/n1 x Z/n2 x ... x Z/nk = H_1(M).
    * 
    * 
    */
  def spincAsHomologyClass(e_0: SafeLong, coeffs: Vector[Rational], as: Vector[Spinc]) = {
    val v = coeffs.length
    val alpha = coeffs.map(_.numerator)
    val omega = coeffs.map(_.denominator)
    val contFracs = coeffs.map(toContinuedFraction)
    //println("contFracs: " + contFracs)
    val s = contFracs.map(_.length)

    /**  Fix 0 <= l < v, i.e. the l-th leg.
      *  n^l_{i,j} / d^l_{i,j} = [k^l_i, ..., k^l_j],
      *  where [k^l_0, ..., k^l_{s_l-1}] = alpha(l)/omega(l).
      * 
      *  Note: difference in index with notation in paper.
      *        Our n(l,i,j) = the paper's n^(l+1)_{i+1,j+1}.
      */
    def n(l: Int, i: Int, j: Int): SafeLong = {
      if (j < i - 1) 0
      else if (j == i - 1) 1
      else {
        require(l >= 0 && i >= 0 && j >= 0)
        fromContinuedFraction(contFracs(l).slice(i, j + 1)).numerator
      }
    }

    /**  Consider SI of Proposition 11.5.
      *  (1) a_0 >= 0, a^l_j >= 0, for 1 <= l <= v, 1 <= j <= s_l.
      *  (2) sum_{t=j}^{s_l} n^l_{t+1,s_l} a^l_t < n^l_{j,s_l} for 1 <= l <= v, 1 <= j <= s_l.
      *  (3) Let a_l = sum_{t=1}^{s_l} n^l_{t+1,s_l} a^l_t.
      *      Then (a_0, a_1, ..., a_n) satisfies SI_red, i.e. is a spinc structure.
      * 
      *  Fix an l. Then condition (2) gives us an upperbound
      *  on each a^l_j. Search this space to get all a^l_j >= 0 satisfying (2).
      * 
      *  Then for each l, we will have a collection of possible a_l and corresponding {a^l_j}_j.
      *  This gives us a map E_l(a_l) = (a^l_1, ..., a^l_{s_l}).
      * 
      */
    def search(l: Int,
      as: Vector[Vector[SafeLong]] = Vector(Vector())
    ): Vector[Vector[SafeLong]] = {
      def cond2Holds(a: Vector[SafeLong]) =
        (1 to s(l)).forall(j =>
          sum(j, a.length)(t => n(l, t, s(l)-1) * a(t-1)) < n(l, j-1, s(l)-1)
        )
      
      if (as(0).length == s(l)) as
      else {
        search(l,
          as.flatMap(a =>
            Stream.from(0)
              .map(a_t => a :+ SafeLong(a_t))
              .takeWhile(cond2Holds)
              .toVector
          )
        )
      }
    }

    /*  Section 11.4 Equation 2:
     *  a(l) = sum_{t=1}^{s_l} n^l_{t+1,s_l} a^l_t.
     *  fromDoubleSS recovers a(l) from a^l_t.
     *  @param l l-th leg.
     */
    def fromDoubleSS(l: Int, a_ss: Vector[SafeLong]): SafeLong =
      sum(1, s(l))(t => n(l, t, s(l)-1)*a_ss(t-1))

    /**  For a given l, and a_l, returns corresponding (a^l_1,...,a^l_{s_l}).
      *  l is the lth leg.
      */
    def E(l: Int, a_l: SafeLong): Vector[SafeLong] = {
      search(l).find(a => a_l == fromDoubleSS(l, a)) match {
        case Some(a) => a
        case None => throw new Exception(
          s"Did not find soln to SI corresponding to SI_red a_$l = ${a_l}.\n" +
           "Possibilities: " + search(l)
        )
      }
    }

    /*
     * From Section 11.3,
     *   H := H_1(M) = <g_0, g^1_{s_1}, ..., g^v_{s_v} |
     *                  e_0 g_0 + sum_{i=1}^v omega_i g^i_{s_l},
     *                  g_0 = alpha_l g^l_{s_l} for all l>
     * 
     */
    // Presentation matrix for H where each column is a relation.
    val P = Matrix.fromFunction(v + 1, v + 1, {
      case (0, 0) => e_0
      case (i, 0) => omega(i-1)
      case (0, i) => -1
      case (i, j) if i == j => alpha(i - 1)
      case _ => 0
    })

    // smith = left P right, where D is smith normal form
    val (smith, left, right) = P.extendedSmithForm

    /**  The element in H_1(M) corresponding to some (a_0, ..., a_l) is given by
      *    -a_0 g_0 - sum_{j,l} a^l_j n^l_{j+1,s_l} g^l_{s_l}    [11.3 & 11.4 Eq 1].
      *  Write this as a column vector v. Then (a_0, ..., a_l) corresponds to
      *  left*v in Z^(v+1)/im(D).
      */
    // Returns column vector v, as in comment above.
    def asCol(a: Spinc) = Matrix.fromFunction(v + 1, 1, {
      case (0, _) => -a(0)
      case (l, _) => {
        val al = E(l-1, a(l))
        sum(1, min(al.length, s(l-1)))(j => -al(j-1) * n(l-1, j, s(l-1)-1))
      }
    })

    def mod(a: Vector[SafeLong], h: Vector[SafeLong]) = 
      (0 until a.length).toVector.map(i => ((a(i) % h(i)) + h(i)) % h(i))
    

    //println("spinc: " + as)
    val invFactors = smith.diagonalElements.map(abs(_))
    //println("invFactors: " + invFactors)
    //println("cols: " + as.map(a => asCol(a)))
    val spincHomology = as.map(a => mod((left*asCol(a)).flatten, invFactors))

    // Invariant factors of 1 give Z/Z = 0 factor in homology, discard unless
    // we have a Z-homology sphere, then leave one factor.
    val numOnes = min(invFactors.takeWhile(_ == 1).length, invFactors.length - 1)
    // homology = Vector(n1,n2...) means H_1(M) = Z/n1 + Z/n2 + ...
    val homology = invFactors.drop(numOnes) 
    (homology, spincHomology.map(_.drop(numOnes)))
  }

}
