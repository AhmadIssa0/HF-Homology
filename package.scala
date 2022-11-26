
package ahmad
import spire.math.Rational

package object hfhomology {
  // Used in BlackGraph
  type Vertex = String 
  type DirEdge = (Vertex, Vertex)

  // Used in MultiGraph
  type VertexTag = String

  type RatPoint = (Rational, Rational, Rational)

  def sequence[A](xs: Vector[Vector[A]]): Vector[Vector[A]] =
    xs match {
      case y +: ys =>
        for (t <- y;
          t2 <- sequence(ys))
        yield t +: t2
      case Vector() => Vector(Vector())
    }
}
