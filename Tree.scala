
package ahmad.hfhomology

import spire.math._
import spire.implicits._

/**
Example constructing a tree:
  import Tree.{rationalChain => rat, tree => t}
  val tree = t(-2, rat(r"-2"), rat(r"-3"), t(-2, rat(r"-2"), rat(r"-11/7")))
**/
case class Tree[A](a: A, subtrees: Vector[Tree[A]]) {
  def fold[B](f: A => B): Tree[B] =
    Tree[B](f(a), subtrees.map(_ fold f))

  // Returns one of the possibly many parents of a vertex with value a
  // Most useful with labelled trees (then parent is unique, if it exists).
  def parent(a: A): Option[Tree[A]] = {
    if (a == this.a) None
    else if (subtrees.exists(s => s.a == a)) Some(this)
    else subtrees.find(s => !s.parent(a).isEmpty).map(s => s.parent(a)).getOrElse(None)
  }

  // All vertices adjacent to one with a given value
  // Only makes sense for labelled trees (distinct vertex values).
  def adjacent(a: A): Vector[A] =
    parent(a).map(_.a).toVector ++ subtrees.map(_.a)

  def mapOverVertices[B](f: A => B): Vector[B] = 
    f(a) +: subtrees.flatMap(_ mapOverVertices f)

  def forall(p: A => Boolean): Boolean =
    p(a) && subtrees.forall(st => st.forall(p))

  def exists(p: A => Boolean): Boolean =
    p(a) || subtrees.exists(st => st.exists(p))

  def vertices: Vector[A] =
    a +: subtrees.flatMap(_.vertices)

  /* Indices down subtrees to get to a vertex satisfying `p`.
   */
  def pathToVert(p: A => Boolean): Option[Vector[Int]] = {
    if (p(a)) Some(Vector())
    else {
      subtrees.map(s => s.pathToVert(p))
        .zipWithIndex
        .find({ case (p, i) => !p.isEmpty })
        .map({ case (p, i) => i +: p.get })
    }
  }


  def numVertices = vertices.length

  def filterVertices(p: Tree[A] => Boolean): Vector[A] = {
    (if (p(this)) Vector(a) else Vector()) ++
    subtrees.flatMap(st => st.filterVertices(p))
  }

  // applies operation op with takes value-at-root and
  // values-at-children recursively
  def reduce[B](op: (A, Vector[B]) => B): Tree[B] = {
    val mappedSubtrees = subtrees.map(st => st.reduce(op))
    Tree(op(a, mappedSubtrees.map(_.a)), mappedSubtrees)
  }


  def mapOverEdges[B](f: (A, A) => B): Vector[B] = 
    subtrees.flatMap(subtree =>
      f(a, subtree.a) +: subtree.mapOverEdges(f)
    )

  // Label the tree with integers starting from 0
  lazy val toLabelledTree: Tree[(A, Int)] = { 
    def labelTree(t: Tree[A], newLabel: Int = 0): (Tree[(A, Int)], Int) = {
      val (labelledSubtrees, nextLabel) = 
        t.subtrees.foldLeft((Vector[Tree[(A, Int)]](), newLabel)) {
          case ((visitedSubtrees, nextLabel), st) =>
          val (labelledSubtree, label) = labelTree(st, nextLabel)
          (visitedSubtrees :+ labelledSubtree, label)
        }
      (Tree[(A, Int)]((t.a, nextLabel), labelledSubtrees), nextLabel + 1)
    }
    labelTree(this)._1
  }

  def isLinearChain(allowFork: Boolean = false): Boolean =
    subtrees.length == 0 ||
    (subtrees.length == 1 && subtrees.head.isLinearChain(false)) ||
    (allowFork && subtrees.length == 2 && subtrees.forall(_.isLinearChain(false)))

  
  // Split the tree at all nodes such that p(a)
  // First tree returned is subtree of current vertex (if current
  // vertex should have subtree)
  def split(p: A => Boolean): Vector[Tree[A]] = {
    if (p(a)) subtrees.flatMap(st => st.split(p))
    else {
      val subforrests = subtrees.map(st => st.split(p))

      val newSubtrees =
        for ((st, sf) <- subtrees.zip(subforrests) if !p(st.a))
        yield sf.head

      val disconnectedComps =
        for ((st, sf) <- subtrees.zip(subforrests))
        yield {
          if (p(st.a)) sf else sf.tail
        }

      Tree(a, newSubtrees) +: disconnectedComps.flatten
    }
  }

  override def toString: String = {
    def asString(a: A): String = a match {
      case (w: Int, v: IntersectionForm.Coeffs) =>
        w + ": " + v.map({
          case (1, m) => "+e_" + m
          case (-1, m) => "-e_" + m
          case (p, m) if p > 0 => "+" + p + "e_" + m
          case (p, m) => p + "e_" + m
        }).mkString(" ")
      case x => x.toString
    }

    // last is whether this tree is the last child in its parent
    // verticals records whether we need to prefix a pipe at a given depth
    def pretty(t: Tree[A], verticals: Vector[Boolean], last: Boolean): String = {
      val L = "\u2514"
      val T = "\u251C"
      val V = "\u2502" // pipe |
      val H = "\u2500" // -

      val prefix = verticals.slice(0, verticals.length - 1).map({
        case true => s" $V  "
        case false => "    "
      })
        .mkString("")

      val nonRootPrefix = if (verticals.isEmpty) "" else {
          if (last) s" $L$H$H" else s" $T$H$H"
      }

      val root = prefix + nonRootPrefix + s"(${asString(t.a)})" + "\r\n"
      val reversedSts = t.subtrees.reverse // children are displayed CCW
      val middle: Vector[String] =
        reversedSts
          .slice(0,t.subtrees.length-1)
          .map(st => pretty(st, verticals :+ true, false))
      val end = reversedSts.lastOption match {
        case Some(s) => Vector(pretty(s, verticals :+ false, true))
        case None => Vector()
      }
      root + (middle ++ end).mkString("")
    }
    pretty(this, Vector(), false)
  }
}

object Tree {
  import IntersectionForm._

  implicit class VectorTreeOps[A](t: Tree[Vector[A]]) {
    /* Given a tree with Vector assigned to nodes
     * return a Stream of all possible ways to create a Tree[A]
     * by selecting one of the elements from each node
     */
    def enumerate: Stream[Tree[A]] = {
      def sequence(xs: Vector[Stream[Tree[A]]]): Stream[Vector[Tree[A]]] =
        xs match {
          case y +: ys =>
            for (t <- y;
              t2 <- sequence(ys))
            yield t +: t2
          case Vector() => Stream(Vector())
        }

      for (a <- t.a.toStream;
        subtrees <- sequence(t.subtrees.map(_.enumerate)))
      yield Tree(a, subtrees)
    }
  }

  // Tree represents an embeddings.
  implicit class TreeOps(t: Tree[(Int, Coeffs)]) {
    def toMatrixTranspose: Matrix = {
      val verts = t.vertices
      val coeffLabels = verts.flatMap(_._2.map(_._2)).distinct
      val mat = 
      for (i <- (0 until verts.length).toVector) yield {
        val v = verts(i)
        val coeffs = v._2
        for (j <- (0 until coeffLabels.length).toVector) yield {
          coeffs.find(_._2 == coeffLabels(j)) match {
            case Some((w, _)) => SafeLong(w)
            case None => SafeLong(0)
          }
        }
      }
      Matrix(mat)
    }

    def muBar = {
      val A = toMatrixTranspose.transpose
      Spin.muBar(A)
    }

    def muBarObstructs: Boolean = {
      muBar.exists { _ != 0 }
    }
  }

  implicit class IntTreeOps(t: Tree[Int]) {
    import IntersectionForm._
    // embeddings into negative diagonal lattices
    def latticeEmbeddings(maxRank: Option[Int] = None): Stream[Tree[(Int, Coeffs)]] = {
      val labelledTree = t.toLabelledTree
      val embeddings = t.toIntersectionForm.embeddings(maxRank)
      embeddings.map { emb => labelledTree.fold {
        case (w, label) => (w, emb(label).sortBy(_._2))
      }}
    }

    def complementaryEmbeddings: Vector[(Tree[(Int, Coeffs)], Tree[(Int, Coeffs)])] = {
      val labelledTree = t.toLabelledTree
      val embeddings = t.latticeEmbeddings(Some(t.numVertices))

      def embsAreComplementary(
        emb1: Tree[(Int, Coeffs)],
        emb2: Tree[(Int, Coeffs)]
      ): Boolean = {
        emb1.toMatrixTranspose.adjoin(emb2.toMatrixTranspose).isSurjective
      }

      for (i <- (0 until embeddings.length).toVector;
           j <- 0 to i;
        emb1 = embeddings(i);
        emb2 = embeddings(j) if embsAreComplementary(emb1, emb2))
      yield {
        (emb1, emb2)
      }
    }

    def muBarCompatComplementaryEmbs: Vector[(Tree[(Int, Coeffs)], Tree[(Int, Coeffs)])] = {
      complementaryEmbeddings.filter({ case (emb1, emb2) =>
        !emb1.muBarObstructs && !emb2.muBarObstructs
      })
    }

    def perpEmbedding(
      q: IntersectionForm,
      maxRank: Option[Int] = None
    ): Stream[(Tree[(Int, Coeffs)], Embedding)] = {
      val labelledTree = t.toLabelledTree
      val embeddings = t.toIntersectionForm.directSum(q).embeddings(maxRank)
      embeddings.map { emb =>
        val tr = labelledTree.fold { case (w, label) => (w, emb(label).sortBy(_._2)) }
        (tr, emb)
      }
    }

    /** Attempts to embed a negative definite tree into an integer changemaker lattice.
      */
    def changemakerEmbeddings = {
      val labelledTree = t.toLabelledTree
      val treeIntForm = t.toIntersectionForm
      val det = treeIntForm.det.toInt
      val rank = treeIntForm.rank
      val embeddings = treeIntForm.changemakerEmbeddings
      embeddings.map { emb =>
        val tree = labelledTree.fold { case (w, label) =>
          (w, emb(label).sortBy(_._2).map{case (c, n) => (c, n-1)})
        }
        //Forest(Vector(tree, Tree.tree((-det, emb(rank)))))
        val cmVec = emb(rank).sortBy(_._2).map {case (c, n) => (c, n-1)}
        Changemaker(tree, cmVec, det)
      }
    }

    def halfIntCMEmbeddings = {
       val labelledTree = t.toLabelledTree
      val treeIntForm = t.toIntersectionForm
      val det = treeIntForm.det.toInt
      val rank = treeIntForm.rank
      val embeddings = treeIntForm.halfIntCMEmbeddings
      embeddings.map { emb =>
        val tree = labelledTree.fold { case (w, label) =>
          (w, emb(label).sortBy(_._2).map{case (c, n) => (c, n-1)})
        }
        //Forest(Vector(tree, Tree.tree((-det, emb(rank)))))
        val cmVec1 = emb(rank).sortBy(_._2).map {case (c, n) => (c, n-1)}
        val cmVec2 = emb(rank+1).sortBy(_._2).map {case (c, n) => (c, n-1)} // norm 2
        HalfIntCM(tree, cmVec1, cmVec2, det)
      }
    }


    /** Greene's obstruction. If QA then A^T must be surjective
      * for some embedding A.
      */
    def greeneObstructs: Boolean =
      (isNegativeDefinite &&
        latticeEmbeddings().forall(m => !m.toMatrixTranspose.isSurjective))

    def isNegativeDefinite: Boolean = if (t.exists(n => n >= 0)) false else {
      import spire.math._
      import spire.implicits._
      val ratTree = t.fold(n => Some(Rational(n)))
      type RatOpt = Option[Rational]

      def lift[A, B](f: A => B): Option[A] => Option[B] = _ match {
        case Some(a) => Some(f(a))
        case None => None
      }

      // map2 (this should be in std lib)
      def lift2[A, B, C](f: (A, B) => C
      ): (Option[A], Option[B]) => Option[C] = {
        case (Some(a), Some(b)) => Some(f(a,b))
        case _ => None
      }

      val add = lift2 { (a: Rational, b: Rational) => a + b }

      // We might encounter 0, we can't do 1/0, so we assign None.
      // In this case the tree is not negative definite, since
      // we can find an element with self-pairing 0.
      def f(aOpt: RatOpt, asOpt: Vector[RatOpt]): RatOpt = {
        val sOpt =
          asOpt.map(opt => opt.filter(_ != 0))
             .map(lift { (r: Rational) => -1/r })
             .foldLeft(Some(Rational(0)): RatOpt)(add)
        add(aOpt, sOpt)
      }

      val reduced = ratTree.reduce(f)
      reduced.forall {
        case Some(r) => r < 0
        case None => false
      }
    }

    def isLSpace: Either[String, Boolean] = {
      if (!isNegativeDefinite) Left("Not negative definite.")
      else Right(toIntersectionForm.isLSpace)
    }

    /** IntersectionForm matrix basis vectors ordered according to toLabelledTree.
      */
    def toIntersectionForm: IntersectionForm = {
      val labelledTree = t.toLabelledTree
      val edges = labelledTree.mapOverEdges((x, y) => (x._2, y._2))
      val vertices = labelledTree.mapOverVertices(x => x)
      val size = vertices.length
      val q: Vector[Vector[Int]] = 
      for (i <- 0 until size toVector) yield {
        for (j <- 0 until size toVector) yield {
          if (i == j) {
            vertices.find(_._2 == i)
              .map(_._1)
              .getOrElse(0)
          } else {
            if ((edges contains (i, j)) || (edges contains (j, i))) 1 else 0
          }
        }
      }
      IntersectionForm(q)
    }

    def det: SafeLong =
      t.toIntersectionForm.toMatrix.absDet

    def detAddableNodes = {
      t.candidateQA.filter { case (t1, t2, forest) =>
        println(s"${t1.det} == ${t2.det} + ${forest.map(_.det).qproduct}")
        t1.det == t2.det + forest.map(_.det).qproduct
      }
    }


    def isVerifiedQA: Boolean = {
      println(t)
      if (t.isLinearChain(true) && t.det != 0) true
      else t.candidateQA.exists { case (t1, t2, forest) =>
        /*
        if (t1.det == t2.det + forest.map(_.det).qproduct) {
          println("passed det condition")
          println(t2)
        }
         */
        val res = 
          t1.det == t2.det + forest.map(_.det).qproduct &&
          t2.isVerifiedQA &&
          forest.forall(tr => tr.isVerifiedQA)
        
        if (res) {
          println("Good cut:")
          println(t2)
          println(t2.toIntersectionForm.toMathematica)
          println(forest.map(_.toIntersectionForm.toMathematica))
        }

        //println("following tree is QA: " + res)
        //println(t)
        res
      }
    }

    /* At potentially QA nodes in our tree, returns Vectors of 3 things:
     * 1) Tree where the node value is replaced with -1 and subchain removed
     * 2) Tree where entire linear chain starting at the QA node is removed
     * 3) Split the graph at the parent of the QA node, return Vector of trees
     */
    def candidateQA: Vector[(Tree[Int], Tree[Int], Vector[Tree[Int]])] = {
      type LabelledTree = Tree[(Int, Int)]
      type Label = Int

      val labelledTree = t.toLabelledTree

      /* Want all labels which are at the start
       * of a linear chain. A linear chain can either be cut off above
       * or below.
       * @param linear Is tree a child of a linear chain so far?
       * @return Vector of pairs of (Label, cutOffAbove)
       *         where cutOffAbove is true if the linear-chain resides
       *         as ancestors of node, false otherwise.
       */
      def startOfChains(tree: LabelledTree, linear: Boolean
      ): Vector[(Label, Boolean)] = {
        if (!linear && tree.isLinearChain(false)) Vector((tree.a._2, false))
        else if (linear && tree.subtrees.length == 1) {
          val st = tree.subtrees.head
          if (st.subtrees.length > 1)
            (tree.a._2, true) +: startOfChains(st, false)
          else startOfChains(st, true) 
        } else {
          val remainsLinear = linear && tree.subtrees.length == 1
          tree.subtrees.flatMap(st => startOfChains(st, remainsLinear))
        }
      }

      val qaNode: Vector[(Label, Boolean)] = startOfChains(labelledTree, true)

      /* Given a label of a potentially QA node in our tree, returns 3 things:
       * 1) Tree where the node value is replaced with -1 and subchain removed
       * 2) Tree where entire linear chain starting at the QA node is removed
       * 3) Split the graph at the parent of the QA node, return Vector of trees
       */
      def resolve(label: Label, cutAbove: Boolean
      ): (Tree[Int], Tree[Int], Vector[Tree[Int]]) = {
        // cuts off linear chain, sets qa node value to -1
        def cutBelowLabel(ltree: LabelledTree): LabelledTree = {
          val sign = if (ltree.a._1 > 0) 1 else -1

          (ltree.a._2 == label, cutAbove) match {
            case (true,  false) => Tree((sign, label), Vector())
            case (false, false) =>
              Tree(ltree.a, ltree.subtrees.map(st => cutBelowLabel(st)))
            case (true,  true) => ltree.copy(a = (sign, label))
            case (false, true) => cutBelowLabel(ltree.subtrees.head)
          }
        }

        // "Parent" might actually be a child, mean the central vertex
        def cutChain(ltree: LabelledTree): Vector[LabelledTree] =
          (ltree.a._2 == label, cutAbove) match {
            case (true,  false) => Vector()
            case (false, false) =>
              Vector(Tree(ltree.a, ltree.subtrees.flatMap(st => cutChain(st))))
            case (true,  true) => Vector(ltree.subtrees.head)
            case (false, true) => cutChain(ltree.subtrees.head)
          }

        // get the parent (adjacent vertex of degree > 2)
        def parent(ltree: LabelledTree): Option[Label] = 
          (ltree.a._2 == label, cutAbove) match {
            case (true, true) => Some(ltree.subtrees.head.a._2)
            case (false, true) => parent(ltree.subtrees.head)
            case (false, false) =>
              if (ltree.subtrees.exists(st => st.a._2 == label)) Some(ltree.a._2)
              else ltree.subtrees.map(st => parent(st)).find(!_.isEmpty).getOrElse(None)
            case (true, false) => throw new IllegalArgumentException()
          }
        
        val parentLabel = parent(labelledTree).get
        val first = cutBelowLabel(labelledTree).fold(_._1)
        val secondLabelled = cutChain(labelledTree).head
        val second = secondLabelled.fold(_._1)
        val third = secondLabelled.split(_._2 == parentLabel).map(_.fold(_._1))
        (first, second, third)
      }
      for ((label, cutAbove) <- qaNode)
      yield resolve(label, cutAbove)
    }
  }

  def linearTree(root: Int, chain: Int*): Tree[Int] = chain match {
    case Seq(x, xs@_*) => Tree(root, Vector(linearTree(x, xs: _*)))
    case Seq() => Tree(root, Vector())
  }

  /** Expand a rational number r with |r| > 1 as a linear chain */
  def rationalChain(r: Rational): Tree[Int] = {
    require(r < -1 || r > 1)
    import MontesinosIntersectionForm.linearChain
    val chain =
      if (r < -1)
        linearChain(r.numerator.toInt, r.denominator.toInt)
      else
        linearChain(-r.numerator.toInt, r.denominator.toInt).map(x => -x)

    // chain guaranteed to have a head
    linearTree(chain.head, chain.tail:_*)
  }

  def chainToRat(ns: Vector[Int]): Rational = ns match {
    case Vector() => r"0"
    case Vector(a) => Rational(a, 1)
    case a +: tail => Rational(a, 1) - 1 / chainToRat(tail)
  }


  def tree[A](a: A, subtrees: Tree[A]*): Tree[A] =
    Tree(a, subtrees.toVector)
}
