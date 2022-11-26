
package ahmad.hfhomology

import spire.math._
import spire.implicits._

/**
 * Represents a Seifert fibered space over S^2.
 *
 *  Described by a rational plumbing graph.
 *
 *  @param e0 central weight in plumbing
 *  @param coeffs rational numbers representing surgery coefficients of exceptional fibers.
 *
 */
case class SFSOverS2(e0: SafeLong, coeffs: Vector[Rational]) {
  def toMontesinosLink = MontesinosLink(e0, coeffs)

  def toTree = Tree.tree(e0.toInt, coeffs.map(r => Tree.rationalChain(r)) :_*)

  def muBar = this.negDef.toTree.toIntersectionForm.muBar

  // Signatures of Montesinos links bounding positive definite manifold.
  def signatures = muBar

  // Planar graph of graph lattice, tree must be negDef.
  def toPlanarGraph = {
    assert(abs(e0) >= coeffs.length, s"|e0| = ${abs(e0)} must be at least no. fibers.")
    //println(this)
    val chains = coeffs.map(r => MontesinosIntersectionForm.linearChain(r))
    //PlanarGraph.fromIntersectionForm(this.negDef.toTree.toIntersectionForm)
    var marker: Int = 0
    val m = scala.collection.mutable
       .Map[String, Vector[(String, Option[Int])]]().withDefaultValue(Vector())
    val n = coeffs.length
    var rootAdj = Vector[(String, Int)]()
    
    m("c") = Vector.tabulate(-e0.toInt-n)(i => ("r", Some(i))) ++
      (0 until n).toVector.map(i => (s"$i-0", None))
    rootAdj = rootAdj ++ Vector.tabulate(-e0.toInt-n)(i => ("c", i))
    marker += -e0.toInt-n

    for (i <- 0 until n) {
      val deg = if (chains(i).length > 1) 2 else 1
      m(s"$i-0") = (("c", None) +:
        Vector.tabulate(-chains(i)(0)-deg)(m => ("r", Some(m+marker))))
      rootAdj = rootAdj ++ Vector.tabulate(-chains(i)(0)-deg)(m => (s"$i-0", marker+m))
      marker += -chains(i)(0)-deg
      if (chains(i).length > 1) {
        m(s"$i-0") = m(s"$i-0") :+ (s"$i-1", None)
      }


      for (j <- 1 until chains(i).length-1) {
        m(s"$i-$j") = (s"$i-${j-1}", None) +:
          Vector.tabulate(-chains(i)(j)-2)(m => ("r", Some(m+marker))) :+
           (s"$i-${j+1}", None)
        rootAdj = rootAdj ++ Vector.tabulate(-chains(i)(j)-2)(m => (s"$i-$j", m+marker))
        marker += -chains(i)(j)-2
      }

      if (chains(i).length > 1) {
        m(s"$i-${chains(i).length-1}") = (s"$i-${chains(i).length-2}", None) +:
          Vector.tabulate(-chains(i)(chains(i).length-1)-1)(m => ("r", Some(m+marker)))
        rootAdj = rootAdj ++ Vector.tabulate(-chains(i)(chains(i).length-1)-1)(m => (s"$i-${chains(i).length-1}", m+marker))
        marker += -chains(i)(chains(i).length-1)-1
      }
    }
    m("r") = rootAdj.map({ case (a, i) => (a, Some(i)) }).reverse
    for (key <- m.keys if key != "r") {
      m(key) = m(key).map ({
        case (v, None) if v != "r" => {
          val i = m(v).indexWhere(_._1 == key)
          if (i == -1) {
            println(s"m($v) = ${m(v)}")
            println(s"m($key) = ${m(key)}")
          }

          m(v) = m(v).updated(i, (key, Some(marker)))
          marker += 1
          (v, Some(marker-1))
        }
        case x => x
      })
    }
    //println(m)
    PlanarGraph(m.mapValues(values => values.map({
      case (v, Some(x)) => (v, x)
      case _ => throw new Exception("Edge didn't get labelled.")
    })).toMap)
    //PlanarGraph(m.toMap)
  }

  def complementaryEmbsWithPartitions = {
    val sfs = negDef
    val tree = Tree.tree(sfs.e0.toInt, sfs.coeffs.map(r => Tree.rationalChain(r)) :_*)

    import IntersectionForm.Coeffs
    // If e_1 is in the root, which children also involves e_1?
    // This gives a partition of the legs of the SFS.
    // Returns partition (in terms of indices)
    def partition(emb: Tree[(Int, Coeffs)]): Vector[Vector[Int]] = {
      emb.a._2.map({ case (_, c) =>
        emb.subtrees.zipWithIndex.filter({ case (leg, _) =>
          leg.a._2.exists(_._2 == c)
        }).map(_._2)
      })
    }

    tree.muBarCompatComplementaryEmbs.map({ case (emb1, emb2) =>
    //tree.complementaryEmbeddings.map({ case (emb1, emb2) =>
      // a tree representing an embedding has type Tree[(Int, Coeffs)]
      ((partition(emb1), emb1), (partition(emb2), emb2))
    })
  }

  def plumbingRank = toTree.numVertices
  /**
   * Order of first homology. 0 if first homology is infinite.
   *
   *  See Section 1.1 of "Invariants for homology 3-spheres" - Savaliev, Gamkrelidze
   *  for the formula.
   */
  lazy val homologyOrder: SafeLong = {
    if (coeffs.length == 0) 0 // We have S^2 x S^1
    else {
      val a = coeffs.map(_.numerator).qproduct
      val order = (coeffs.map(r => 1 / r).qsum - e0) * a
      order.toSafeLong.abs
    }
  }

  def sortParams = SFSOverS2(e0, coeffs.sorted)

  /** Compute homology.
    * From Section 11.3 of Nemethi,
    *   H := H_1(M) = <g_0, g^1_{s_1}, ..., g^v_{s_v} |
    *                  e_0 g_0 + sum_{i=1}^v omega_i g^i_{s_l},
    *                  g_0 = alpha_l g^l_{s_l} for all l>
    * @return Invariant factors of abelian group.
    */
  lazy val homology: Vector[SafeLong] = {
    if (generalisedEuler == 0) Vector(0)
    else {
      val sfs = this//negDef
      val v =  sfs.coeffs.length
      val alpha = sfs.coeffs.map(-_.numerator)
      val omega = sfs.coeffs.map(_.denominator)
      //println("alpha: " + alpha)
      //println("omega: " + omega)
      // Presentation matrix for H where each column is a relation.
      val P = Matrix.fromFunction(v + 1, v + 1, {
        case (0, 0) => sfs.e0
        case (i, 0) => omega(i-1)
        case (0, i) => -1
        case (i, j) if i == j => alpha(i - 1)
        case _ => 0
      })
      P.invariantFactors
    }
  }

  val homologyMatrix = {
    val sfs = this//negDef
    val v =  sfs.coeffs.length
    val alpha = sfs.coeffs.map(-_.numerator)
    val omega = sfs.coeffs.map(_.denominator)
    //println("alpha: " + alpha)
    //println("omega: " + omega)
    // Presentation matrix for H where each column is a relation.
    val P = Matrix.fromFunction(v + 1, v + 1, {
      case (0, 0) => sfs.e0
      case (i, 0) => omega(i-1)
      case (0, i) => -1
      case (i, j) if i == j => alpha(i - 1)
      case _ => 0
    })
    P
  }


  def toPythonString = {
    s"Vector((-1,$e0), " + coeffs.map(r => s"(${r.numerator}, ${r.denominator})").mkString(", ") + ")"
  }


  /**
    * Homology group is given as direct sums of (Z_{p^n})^k, 
    *   where p is a prime, n, k >= 1.
    * So Z_3 (+) (Z_(2^3))^4 would return Vector(((3,1), 1), ((2,3), 4))
    */
  def homologyPrimeDecomposition: Vector[((SafeLong,Int), Int)] = {
    val primePowerSummands = homology.flatMap({ invFactor =>
      prime.factor(invFactor).factors.toVector
    })

    primePowerSummands.groupBy(x => x).mapValues(_.length).toVector
  }

  def homologyIsDirectDouble: Boolean = {
    homologyPrimeDecomposition.forall { case ((_, _), pow) => pow % 2 == 0 }
  }

  /**
    * Generalised Euler invariant e.
    * SFS bounds a definite plumbing iff e != 0.
    * In which case it is negative definite if e < 0,
    * and positive definite if e > 0.
    */
  lazy val generalisedEuler: Rational =
    Rational(e0) - coeffs.map(1/_).qsum

  def isNegativeDefinite = generalisedEuler < 0
  
  def reverseOrientation: SFSOverS2 =
    SFSOverS2(-e0, coeffs.map(x => -x))

  def nonDef: SFSOverS2 = {
    val negdef = negDef
    val newe0 = negdef.e0 + negdef.coeffs.length
    val newCoeffs = negdef.coeffs.map({ r =>
      val num = r.numerator.abs
      val denom = r.denominator.abs
      Rational(num, num - denom)
    })
    SFSOverS2(newe0, newCoeffs)
  }

  def negDef: SFSOverS2 = {
    val e = generalisedEuler
    require (e != 0, s"$this can not be made definite.")
    if (e < 0) this.stdForm
    else reverseOrientation.stdForm
  }

  def negSemiDef: SFSOverS2 = {
    val e = generalisedEuler
    require (e == 0, s"$this is not an indefinite case.")

    val std = this.stdForm
    if (std.e0 < 0) return std
    else reverseOrientation.stdForm
  }

  /**
    * Returns representation of SFS with all coefficients p/q < -1.
    * 
    */
  def stdForm: SFSOverS2 = {
    val e: SafeLong = e0 - coeffs.map(r => (1 / r).ceil).qsum.toSafeLong
    SFSOverS2(e, coeffs.map(r => 1/((1/r) - (1/r).ceil)))
  }

  def isQA = {
    val sfs = stdForm.reverseOrientation
    val p = coeffs.length
    sfs.e0.toInt match {
      case e if e < 0 || e > p-1 => true
      case 1 => sfs.coeffs.combinations(2).exists({
        case Vector(r1, r2) => 1/(1 - 1/r1) > r2 || 1/(1 - 1/r2) > r1
      })
      case _ => sfs.coeffs.combinations(2).exists({
        case Vector(r1, r2) => 1/(1 - 1/r1) < r2 || 1/(1 - 1/r2) < r1
      })
    }
  }

  /**
    * Two-fold quasi-alternating links were introduced in
    * https://arxiv.org/abs/1605.05394.
    * It is known that if a Montesinos knot satisfies a non-strict
    * version of the QA conditions then it's TQA (Prop 5 in paper).
    * 
    * We do not check that we have a knot, although
    * strictly speaking we should.
    */
  def isKnownTQA = {
    val sfs = stdForm.reverseOrientation
    val p = coeffs.length
    sfs.e0.toInt match {
      case e if e < 0 || e > p-1 => true
      case 1 => sfs.coeffs.combinations(2).exists({
        case Vector(r1, r2) => 1/(1 - 1/r1) >= r2 || 1/(1 - 1/r2) >= r1
      })
      case _ => sfs.coeffs.combinations(2).exists({
        case Vector(r1, r2) => 1/(1 - 1/r1) <= r2 || 1/(1 - 1/r2) <= r1
      })
    }
  }


  /**  Torisu showed that a Montesinos knot with 3-singular fibers
    *  has an unknotting crossing in a standard diagram iff it is
    *  of the form M(0; p/r, q/s, (2mn \pm 1)/(2n^2)),
    *  where p, q, r, s, m, n are non-zero integers with
    *        p*s + q*r = 1, and
    *        m, n coprime.
    *  We check whether this SFS is the double branched cover
    *  of such a Montesinos knot.
    */
  def isTorisuForm = if (coeffs.length != 3) false else {
    // We should check if the Montesinos link is a knot.

    /** Checks if two rationals r1 = a/b and r2 = c/d can be put 
      * in the form p/r, q/s with p*s + q*r = 1. 
      * 
      * Notice that we can adjust a/b to a/(b + k1*a) and c/d to 
      * c/(d + k2*c).
      * Hence, if Q := a*(d + k2*c) + c*(b + k1*a) = 1 for some k1, k2
      * then we adjust, r1 and r2 and e_0 increases by:
      *   (k1 + k2) if a > 0 and c > 0, more generally by
      *   (sign(a) k1 + sign(c) k2).
      * 
      *  But, Q = ad + bc + ac(k1 + k2),
      *  so we can WLOG just adjust a/b. We can make this expression
      *  equal to 1 provided ad + bc == 1 (mod ac).
      * 
      *  We may also replace a/b with (-a)/(-b) which changes Q to -Q.
      *  Hence if Q == -1 (mod ac) there is also a solution.
      * 
      *  @return How much to adjust e_0 by if solution found.
      *          None otherwise.
      */
    def checkFirstTwo(r1: Rational, r2: Rational): Option[SafeLong] = {
      val (a, b) = (r1.numerator, r1.denominator)
      val (c, d) = (r2.numerator, r2.denominator)

      def posMod(s: SafeLong, t: SafeLong) =
        ((s % t) + t.abs) % t

      if (posMod(a*d + b*c, a*c) == 1) {
        //println(s"Checking $r1, $r2")
        Some((1 - a*d - b*c)/(a*c))
      } else if (posMod(a*d + b*c, a*c) == (a*c).abs-1) {
        Some((1 + a*d + b*c)/(-a*c))
      } else 
        None
    }

    def checkThird(r3: Rational): Boolean = {
      val (a, b) = (r3.numerator, r3.denominator)
      // if r3 < 0 then a < 0.

      // Check if b = 2n^2 for some n.
      if (b % 2 != 0) false
      else {
        val n = (b/2).sqrt
        if (n*n != b/2) false else {
          // a = 2mn \pm 1. (two cases)
          val case1: Boolean = if ((a+1) % (2*n) == 0) {
            val m = (a+1)/(2*n)
            (m != 0) && gcd(m, n) == 1
          } else false

          val case2: Boolean = if ((a-1) % (2*n) == 0) {
            val m = (a-1)/(2*n)
            (m != 0) && gcd(m, n) == 1
          } else false

          case1 || case2
        }
      }
    }

    // Check if, in this order, is in Torisu form.
    def isTorisu(r1: Rational, r2: Rational, r3: Rational) = {
      checkFirstTwo(r1, r2) match {
        case None => false
        case Some(e_adj) => {
          //println(s"First two succeeded on $r1, $r2 adjust $e_adj")
          val e = e0 + e_adj
          // if r3 < 0 then b < 0
          val (a, b) = (r3.numerator.abs, r3.signum*r3.denominator)
          //println("checking third on " + Rational(a, b - e*a))
          checkThird(Rational(a, b - e*a))
        }
      }
    }

    val (r1, r2, r3) = (coeffs(0), coeffs(1), coeffs(2))
    isTorisu(r1, r2, r3) || isTorisu(r1, r3, r2) || isTorisu(r2, r3, r1)
  }



  /**  Returns the d-invariants as a case class.
    */
  lazy val dInvariants = {
    val e = generalisedEuler
    require(e != 0, "Can't compute d-invariants for non QHS.")
    val sfs = negDef
    val dinvs = DInvariants.sfs(sfs.e0, sfs.coeffs.map(r => -r))
    if (e < 0) dinvs else dinvs.reverseOrientation
  }

  
  def alexPolyFromSurgery(r: Rational): Either[String,Vector[Vector[SafeLong]]] = {
    if (isLSpace) {
      val dInvs = dInvariants
      if (dInvs.homology.length != 1)
        Left(s"$this does not have cyclic homology: ${dInvs.homology}")
      else {
        Right(DInvariants.possibleAlexPoly(dInvariants.raw, r))
      }
    } else Left(s"$this is not an LSpace.")
  }

  /**  Do the d-invariants obstruct a knot from having an L-space r surgery
    *  orientation homeomorphic to this SFS?
    */
  def canObstructSurgery(r: Rational): Boolean = alexPolyFromSurgery(r) match {
    case Left(_) => false
    case Right(v) if v.isEmpty => true
    case _ => false
  }

  /**
   *  L-space SFSs over S^2 are classified in Corollary 5.2 of
   *  "Floer simple manifolds and L-space intervals" - J. Rasmussen, S. Rasmussen
   *  http://arxiv.org/pdf/1508.05900v2.pdf
   *
   *
   *  The papers conventions are different to ours. Our e0 is the paper's -e_0.
   *  The paper's r_i/s_i are the reciprocal of coeffs.
   */
  lazy val isLSpace = {
    // An L-space must be a rational homology sphere.
    if (homologyOrder == 0) false
    else {
      val coeffsRecip = coeffs.map(r => 1 / r)
      val e_0 = -e0 // follow paper's conventions
      if (Rational(e_0) + coeffsRecip.qsum != 0) {
        // We choose j = 1 in the paper.
        def f(x: BigInt) = {
          val a: Rational = coeffsRecip.drop(1).map(r => (r * x).ceil).qsum - 1
          -a / x
        }

        def g(x: BigInt) = {
          val a: Rational = coeffsRecip.drop(1).map(r => (r * x).floor).qsum + 1
          -a / x
        }
        val denoms: Vector[SafeLong] =
          coeffsRecip.drop(1).map(r => r.abs.denominator)
        val s = SFSOverS2.lcm(denoms: _*).abs.toLong
        val cond1 = coeffsRecip(0) <= (-Rational(e_0) + (1L until s)
          .map(x => f(x)).min)
        lazy val cond2 = (-Rational(e_0) + (1L until s).map(x => g(x)).max) <= coeffsRecip(0)
        cond1 || cond2
      } else false
    }
  }

  def prettyPotentialHandles() = {
    val sfsToTest = this
    println(sfsToTest)
    //println(sfsToTest.toTree)
    val handles = sfsToTest.potentialHandles(framing = 1)
    if (!handles.isEmpty && !handles.flatMap(handle => sfsToTest.identifyPotentialS3(handle, 1)).isEmpty) {
      //println(sfsToTest)
      println(sfsToTest.toTree.toLabelledTree)
      println(handles)
      for (handle <- handles;
        knot <- sfsToTest.identifyPotentialS3(handle, 1)) {
        println(s"handle: $handle, knot: $knot")
        //val recognizer = s"%bri_${p}_${q}_${r}${handle}_${knot}\r\n" + sfsToTest.toRecogniserWithHandle(handle, 1, Some(knot), Some("1/0"))
        //println(recognizer)
        //saveToFile(recognizer, s"C:/Users/Ahmad/Dropbox/code/Recognizer(2015_04_18)/bri_${p}_${q}_${r}${handle}_${knot}.txt")
        
      }
    }
  }


  def knownToBoundAcyclic = {
    if (homologyOrder != 1 || coeffs.length != 3) "Unknown"
    else {
      val bri_mult = coeffs.map(_.numerator.abs.toInt).sorted
      val bri = (bri_mult(0), bri_mult(1), bri_mult(2))

      bri match {
        case (2,3,25) => "Fickle"
        case c if Vector((2,5,7), (3,4,5), (2,3,13)) contains c => "AK"
        case c if Vector((2,7,19), (3,5,19), (3,5,49), (2,7,47)) contains c => "FS"
        case (p,q,r) if ({val s = (q+1)/p; p % 2 == 0 && bri == (p,p*s-1,p*s+1)})
          => s"CH($p,${(q+1)/p})"
        case (p,q,r) if ({val s = (q+1)/p; p % 2 == 1 && bri == (p,p*s-1,p*s-2)})
          => s"CH-($p,${(q+1)/p})"
        case (p,q,r) if ({val s = (q-1)/p; p % 2 == 1 && bri == (p,p*s+1,p*s+2)})
          => s"CH+($p,${(q-1)/p})"
        case (p,q,r) if ({val s = (q+2)/p; p % 2 == 1 && bri == (p,p*s-2,p*s-1)})
          => s"CH-($p,${(q+2)/p})"
        case (p,q,r) if ({val s = (q-2)/p; p % 2 == 1 && bri == (p,p*s+2,p*s+1)})
          => s"CH+($p,${(q-2)/p})"

        case (2,q,r) if ({val s = (q+1)/2; s % 2 == 1 &&
            bri == (2,2*s-1,2*2*(2*s-1)+(2*s+1))}) => s"Stern0-(${(q+1)/2})"
        case (2,q,r) if ({val s = (q-1)/2; s % 2 == 1 &&
            bri == (2,2*s+1,2*2*(2*s+1)+(2*s-1))}) => s"Stern0+(${(q-1)/2})"

        case (3,q,r) if ({val s = (q+1)/3; bri == (3,3*s-1,2*3*(3*s-1)+(3*s-2))})
          => s"Stern1-(${(q+1)/3})"
        case (3,q,r) if ({val s = (q-1)/3; bri == (3,3*s+1,2*3*(3*s+1)+(3*s+2))})
          => s"Stern1+(${(q-1)/3})"

        case (3,q,r) if ({val s = (q+2)/3; bri == (3,3*s-2,2*3*(3*s-2)+(3*s-1))})
          => s"Stern2-(${(q+2)/3})"
        case (3,q,r) if ({val s = (q-2)/3; bri == (3,3*s+2,2*3*(3*s+2)+(3*s+1))})
          => s"Stern2+(${(q-2)/3})"
        case _ => "Unknown"
      }
    }
  }

  // 3-manifold recogniser format
  def toRecogniser: String = {
    val chains = coeffs.map({ r =>
      val chain = MontesinosIntersectionForm.linearChain(-r.abs)
      if (r > 0) chain.map(x => -x) else chain
    })

    var index = 1
    var gaussCodes = Vector[Vector[Int]]()
    var centralVertGauss = Vector[Int]()
    var framings = Vector[Int]()
    var signs = Vector.fill(this.toTree.numVertices)(-1)

    for (j <- 0 until chains.length) {
      val chain = chains(j)
      for (i <- 0 until chain.length) {
        if (i == chain.length - 1) {
          gaussCodes = gaussCodes :+ Vector(index+1, -index)
        } else if (i < chain.length - 1) {
          gaussCodes = gaussCodes :+ Vector(index+1, -index, index+2, -(index+3))
        }
        framings = framings :+ chain(i)
        if (i == 0) centralVertGauss = centralVertGauss ++ Vector(index, -(index+1))
        index += 2
      }
    }
    gaussCodes = gaussCodes :+ centralVertGauss
    framings = framings :+ e0.toInt
    var s = "link\n"
    s = s + "signs " + signs.mkString(" ") + "\n"
    for (i <- 0 until gaussCodes.length) {
      s = s + "code " + gaussCodes(i).mkString(" ") + "\n"
      s = s + "framing " + framings(i).toString + "\n"
    }
    s = s + "end"
    s
  }

  // `verts` given as in output of `potentialHandles()`
  // i.e. in terms of labelledTree labelling.
  def toRecogniserWithHandle(
    verts: (Int, Int),
    framing: Int,
    specVert: Option[Int] = None, // special vertex label which we'll change framing of
    specFraming: Option[String] = None
  ): String = {
    val (v1, v2) = verts
    val tree = toTree.toLabelledTree
    val paths = Vector(v1, v2).map({ v =>
      tree.pathToVert({ case (_, i) => i == v })
    })
    assert(paths.forall(p => !p.isEmpty), "Couldn't find path to vertex.")
    assert(paths.forall(p => !p.get.isEmpty), "Can't include central vertex.")

    val ends: Vector[(Int, Int)] = paths.map({ pOpt =>
      val p = pOpt.get
      (p(0), p.length-1)
    })
    //println(s"Ends: $ends")

    toRecogniserWithHandleByEnds(ends(0), ends(1), framing,
      specVert.map(labelToIndex(_)), specFraming)
  }

  /** Convert from a (non-central vertex) label in the labelled vertex tree
    * to (i, j) where labelled vertex is coeffs(i)'s j-th component in plumbing.
    */
  def labelToIndex(label: Int): (Int, Int) = {
    val tree = toTree.toLabelledTree
    val path = tree.pathToVert({ case (_, i) => i == label })
    assert(!path.isEmpty, "Couldn't find path to vertex.")
    assert(!path.get.isEmpty, "Can't include central vertex.")
    val p = path.get
    (p(0), p.length-1)
  }

  // 3-manifold recogniser format
  // Introduces an additional two handle which links
  // end1._1th chain at vertex end1._2 (counted away from central vertex), as well as
  // end2._2th chain at vertex end2._2 (counted away from central vertex).
  def toRecogniserWithHandleByEnds(
    end1: (Int, Int),
    end2: (Int, Int),
    framing: Int,
    specVert: Option[(Int, Int)] = None, // change framing of this component
    specFraming: Option[String] = None
  ): String = {
    val chains = coeffs.map({ r =>
      val chain = MontesinosIntersectionForm.linearChain(-r.abs)
      if (r > 0) chain.map(x => -x) else chain
    })

    var index = 1
    var gaussCodes = Vector[Vector[Int]]()
    var centralVertGauss = Vector[Int]()
    var framings = Vector[String]()
    val numVertsInTree = this.toTree.numVertices
    val lastIndex = 2*(numVertsInTree-1)
    var signs = Vector.fill(lastIndex)(-1) ++ Vector(-1,-1,1,1)
    
    for (j <- 0 until chains.length) {
      val chain = chains(j)
      for (i <- 0 until chain.length) {
        if (i == chain.length - 1) {
          if (j == end1._1 && i == end1._2) {
            gaussCodes = gaussCodes :+
              Vector(lastIndex+2, -(lastIndex+1), index+1, -index)
          } else if (j == end2._1 && i == end2._2) {
            gaussCodes = gaussCodes :+
              Vector(-(lastIndex+4), lastIndex+3, index+1, -index)
          } else {
            gaussCodes = gaussCodes :+ Vector(index+1, -index)
          }
        } else if (i < chain.length - 1) {
          if (j == end1._1 && i == end1._2) {
            gaussCodes = gaussCodes :+  Vector(lastIndex+2, -(lastIndex+1),
                                           index+1, -index, index+2, -(index+3))
          } else if (j == end2._1 && i == end2._2) {
            gaussCodes = gaussCodes :+ Vector(index+1, -index,
               -(lastIndex+4), lastIndex+3, index+2, -(index+3))
          } else {
            gaussCodes = gaussCodes :+ Vector(index+1, -index, index+2, -(index+3))
          }
        }
        if (specVert.isEmpty || specVert.get != (j, i)) {
          framings = framings :+ chain(i).toString
        } else {
          //println(s"Changing: $j,$i framing ${chain(i)}")
          framings = framings :+ specFraming.get
        }

        if (i == 0) centralVertGauss = centralVertGauss ++ Vector(index, -(index+1))
        index += 2
      }
    }
    gaussCodes = gaussCodes :+ centralVertGauss
    framings = framings :+ e0.toString
    gaussCodes = gaussCodes :+ Vector((lastIndex+1), -(lastIndex+2), -(lastIndex+3), (lastIndex+4))
    framings = framings :+ framing.toString
    var s = "link\r\n"
    s = s + "signs " + signs.mkString(" ") + "\r\n"
    for (i <- 0 until gaussCodes.length) {
      s = s + "code " + gaussCodes(i).mkString(" ") + "\r\n"
      s = s + "framing " + framings(i) + "\r\n"
    }
    s = s + "end"
    s
  }

  // i.e. in terms of labelledTree labelling.
  def addedHandleIntForm(handle: (Int, Int), framing: Int = 1): IntersectionForm = {
    val q = toTree.toIntersectionForm
    val (a, b) = handle
    val row = (0 until q.rank + 1).map ({
      case q.rank => framing
      case `a` => 1
      case `b` => -1
      case _ => 0
    })
    q.addGenerator(row.toVector)
  }

  // After attaching a handle. Is the result surgery in S^3 along a knot which is
  // one of the components of the plumbing? Check homologically that infinity
  // filling on the component gives a homology S^3.
  // Returns vertex labellings on tree of potential such components.
  def identifyPotentialS3(handle: (Int, Int), framing: Int): Vector[Int] = {
    val qWithHandle = addedHandleIntForm(handle, framing)
    val tree = toTree.toLabelledTree
    val centVertLabel = tree.a._2
    //println(qWithHandle)
    (0 until qWithHandle.rank - 1).toVector
      .filter(label =>
        label != centVertLabel && qWithHandle.deleteGenerator(label).det == 1)
  }

  // Ways to add a two handle linking two components in two legs
  // such that the homology is Z.
  def potentialHandles(framing: Int = 1, goalDet: Int = 0) = {
    val q = toTree.toIntersectionForm
    val ltree = toTree.toLabelledTree
      (0 until q.rank).combinations(2).toVector
      .map({ case Vector(a, b) => (a, b) })
      .filter({ case (a, b) =>
        val row = (0 until q.rank + 1).map ({
          case q.rank => framing
          case `a` => 1
          case `b` => -1
          case _ => 0
        })
        //println(s"$a,$b, ${q.addGenerator(row.toVector)}")
        q.addGenerator(row.toVector).toMatrix.invariantFactors == Vector(goalDet)
      })
  }

  def identifyGenPotentialS3(handle: Vector[Int],
    linkingNums: Vector[Int],
    framing: Int
  ): Vector[Int] = {
    val qWithHandle = buildAddedHandleQ(handle, linkingNums, framing)
    val tree = toTree.toLabelledTree
    val centVertLabel = tree.a._2
    //println(qWithHandle)
    (0 until qWithHandle.rank - 1).toVector
      .filter(label =>
        label != centVertLabel && qWithHandle.deleteGenerator(label).det == 1)
  }

  def buildAddedHandleQ(compLabels: Vector[Int], linkingNums: Vector[Int], framing: Int) = {
    val q = toTree.toIntersectionForm
    val row = (0 until q.rank + 1).map ({
      case q.rank => framing
      case i if compLabels.contains(i) => linkingNums(compLabels.indexOf(i))
      case _ => 0
    })
    q.addGenerator(row.toVector)
  }

  // links is the number of components to link
  def genPotentialHandles(framing: Int = 1, links: Int = 2) = {
    val q = toTree.toIntersectionForm
    val ltree = toTree.toLabelledTree

    def buildQ(compLabels: Vector[Int], linkingNums: Vector[Int]) = {
      val row = (0 until q.rank + 1).map ({
        case q.rank => framing
        case i if compLabels.contains(i) => linkingNums(compLabels.indexOf(i))
        case _ => 0
      })
      q.addGenerator(row.toVector)
    }

    for (labels <- (0 until q.rank).toVector.combinations(links).toVector;
      linkingNums <- sequence(Vector.fill(links)(Vector(1,-1)));
      q = buildQ(labels, linkingNums) if q.toMatrix.invariantFactors == Vector(0))
    yield { (labels, linkingNums) }
  }


  def prettyGenPotentialHandles(comps: Int, framing: Int = 1) = {
    val sfsToTest = this
    println(sfsToTest)
    //println(sfsToTest.toTree)
    val handles = sfsToTest.genPotentialHandles(framing = framing, links = comps)
    if (!handles.isEmpty && !handles.flatMap({ case (compLabels, linkingNums) =>
      sfsToTest.identifyGenPotentialS3(compLabels, linkingNums, framing)}).isEmpty) {
      //println(sfsToTest)
      println(sfsToTest.toTree.toLabelledTree)
      println(handles)
      for ((compLabels, linkingNums) <- handles;
        knot <- sfsToTest.identifyGenPotentialS3(compLabels, linkingNums, framing)) {
        println(s"handle: $compLabels, linkingNums: $linkingNums, knot: $knot")
        //val recognizer = s"%bri_${p}_${q}_${r}${handle}_${knot}\r\n" + sfsToTest.toRecogniserWithHandle(handle, 1, Some(knot), Some("1/0"))
        //println(recognizer)
        //saveToFile(recognizer, s"C:/Users/Ahmad/Dropbox/code/Recognizer(2015_04_18)/bri_${p}_${q}_${r}${handle}_${knot}.txt")
        
      }
    }
  }
}

object SFSOverS2 {
  def lcm(nums: SafeLong*): SafeLong = nums match {
    case Seq() => 1
    case Seq(a) => a
    case a +: (b +: rest) => lcm((((a * b) / gcd(a, b)) +: rest): _*)
  }

  /**
    *  Given multiplicities = Vector(p_1, ..., p_n)
    *  where {p_i} are pairwise coprime, returns a SFSOverS2
    *  representing a Brieskorn homology sphere with these multiplicities,
    *  with negative generalised euler number (bounds neg. definite plumbing).
    * 
    */
  def brieskorn(multiplicities: Vector[SafeLong]): SFSOverS2 = {
    require(multiplicities.length >= 3 &&
      multiplicities.combinations(2).forall({ case Vector(a, b) => gcd(a, b) == 1 }))

    if (multiplicities.exists(a => a < 0)) brieskorn(multiplicities.map(_.abs))
    else {
      /** For negative generalised euler number:
        * |H_1| = ((sum q_i/p_i) - b) * p_1 ... p_n  = 1
        * where multiplicities = Vector(p_1, ..., p_n).
        * 
        * Let p = p_1 ... p_n.
        * Then (p/p_i) q_i = 1 (mod p_i).
        * So q_i = (p/p_i)^(-1) (mod p_i).
        * 
        * Once q_i's are assigned. 
        * b = (sum q_i/p_i) - 1/p.
        */
      val p = multiplicities.qproduct
      val coeffs = multiplicities.map {p_i =>
        val q_i = (p/p_i).toBigInt.modInverse(p_i.toBigInt).toSafeLong
        Rational(p_i, q_i)
      }
      val b = coeffs.map(r => 1/r).qsum - Rational(1, p)
      require(b.isWhole, s"Error, b=$b is not a whole number.")
      SFSOverS2(b.toSafeLong, coeffs)
    }
  }

  def randomSFS(fibers: Int,
    upper: Int,
    e0: Int
  ): SFSOverS2 = {
    require(fibers >= 0, "Can't have a negative number of fibers.")
    import scala.util.Random
    val r = new Random()
    def randRational: Rational = {
      val p = r.nextInt(upper - 1) + 2 // in [1,upper]
      val q = r.nextInt(p-1) + 1
      if (gcd(p, q) != 1) randRational else Rational(p,q)
    }

    SFSOverS2(e0, Vector.fill(fibers)(randRational))
  }

  /**
   * Generate SFSs over S^2.
   *
   *  SFS returned are in normal form, i.e. with surgery coefficients 
   *  a_i/b_i satisfying:
   *  0 < b_i / a_i < 1, with 2 <= a_i <= upper.
   *
   */
  def generateSFSs(fibers: Int,
    upper: Int,
    e0: Int
  ): Vector[SFSOverS2] = {
    require(fibers >= 0, "Can't have a negative number of fibers.")

    def allCoeffs(
      fibersLeft: Int,
      possCoeffs: Vector[Vector[Rational]] = Vector(Vector())
    ): Vector[Vector[Rational]] = {
      if (fibersLeft == 0) possCoeffs
      else {
        val nextCoeffs: Vector[Vector[Rational]] =
          for (
            a <- 2 to upper toVector;
            b <- 1 until a if gcd(a, b) == 1;
            coeffs <- possCoeffs if coeffs.isEmpty ||
                                    Rational(a,b) >= coeffs.last
          ) yield coeffs :+ Rational(a,b)
        allCoeffs(fibersLeft - 1, nextCoeffs)
      }
    }
    allCoeffs(fibers).map(SFSOverS2(e0, _))
  }

  def genSFSEmb(fibers: Int,
    upper: Int,
    boundary: Boolean, // if true, only enumerates those with sum q_i/p_i = 1
    pred: Vector[Rational] => Boolean = (_ => true),
    timeoutMillis: Int = 5000) = {

    var hasEmb: List[Vector[Rational]] = List()
    var noEmb: List[Vector[Rational]] = List()

    def generate(currCoeffs: Vector[Rational]): Unit = {
      if ((boundary && currCoeffs.length == fibers-1) ||
        (!boundary && currCoeffs.length == fibers)) {
        val coeffs = 
        if (boundary && currCoeffs.map(r => 1/r).qsum < 1) {
          currCoeffs :+ (1/(1 - currCoeffs.map(r => 1/r).qsum))
        } else currCoeffs

        if (coeffs.length == fibers && coeffs == coeffs.sorted) {
          if (pred(coeffs)) {
            println(s"$coeffs sum: ${coeffs.map(r => 1/r).qsum}")
            val sfs = SFSOverS2(-1, coeffs.map(r => -r))
            sfs.toTree.toIntersectionForm.embeddingsMaxDuration(timeoutMillis) match {
              case Some(embs) => {
                if (embs.length > 0)
                  hasEmb = coeffs +: hasEmb
                else
                  noEmb = coeffs +: noEmb
              }
              case None => {}
            }
          }
        }
      } else {
        for (a <- 2 to upper; b <- 1 until a if gcd(a,b) == 1 && (currCoeffs.length == 0 || currCoeffs.last <= Rational(a,b))) {
          generate(currCoeffs :+ Rational(a,b))
        }
      }
    }

    generate(Vector())
    (hasEmb.toVector, noEmb.toVector)
  }


}
