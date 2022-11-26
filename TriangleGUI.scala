
package ahmad.hfhomology

import spire.implicits._
import spire.math._

import scalafx.Includes._
import scalafx.scene.canvas.Canvas
import scalafx.application.JFXApp
import scalafx.application.JFXApp.PrimaryStage
import scalafx.scene.Scene
import scalafx.scene.paint.Color
import scalafx.scene.paint.Color._
import scalafx.scene.canvas.GraphicsContext
import scalafx.scene.input.{KeyCode, KeyEvent, MouseEvent}
import java.io.File

class TriangleGUI(triData: TriangleData) extends JFXApp {

  val WIDTH = 909*4
  val HEIGHT = 800*4
  val canvas = new Canvas(WIDTH, HEIGHT)
  val gc: GraphicsContext = canvas.graphicsContext2D

  // x-y coordinate bounds that `canvas` depicts.
  var xMin: Double = 0.0
  var xMax: Double = 1.42
  var yMin: Double = 0.0
  var yMax: Double = 1.25

  var canvasPtToSFSs = scala.collection.mutable.Map[(Int, Int), Vector[(RatPoint, Boolean)]]()
                            .withDefaultValue(Vector())

  updateCanvas()

  stage = new PrimaryStage {
    scene = new Scene(WIDTH, HEIGHT) {
      content = List(canvas)
      onKeyPressed = (e: KeyEvent) => e.code match {
        case KeyCode.I => zoom(1.05)
        case KeyCode.O => zoom(0.95)
        case KeyCode.UP => move((0.0, 1.0), 0.01)
        case KeyCode.DOWN => move((0.0, -1.0), 0.01)
        case KeyCode.RIGHT => move((1.0, 0.0), 0.01)
        case KeyCode.LEFT => move((-1.0, 0.0), 0.01)
        case KeyCode.S => saveAsImage("tmp.png")
        case _ => {}
      }
      onMousePressed = (e: MouseEvent) => {
        val pt = (e.sceneX.round.toInt, e.sceneY.round.toInt)
        val nearSFSs = nearestSFSs(pt)
        println(nearSFSs.take(1).map({ case (vec, embs) =>
          val fracs = Vector(-vec._1, -vec._2, -vec._3)
          val chains =fracs
            .map(r => {
              val chain = MontesinosIntersectionForm.linearChain(r)
                                    .map(x => -x).mkString("[",",","]")
              s"${-r} = $chain = 1/${(-1/r).toDouble}"
            })
            .mkString("\r\n")

          s"SFS(1;${vec._1},${vec._2},${vec._3}), lattice embeds: $embs\r\n${chains}"
        })
          .mkString("\r\n")
        )

        //println(nearestSFSs(pt))
      }
    }
  }

  def saveAsImage(filename: String): Unit = {
    TriangleGUI.saveCanvasAsImage(canvas, filename)
  }

  def nearestSFSs(pt: (Int, Int)): Vector[(RatPoint, Boolean)] = {
    val (x0, y0) = pt
    val nbhd = for (x <- (x0 - 5) to (x0 + 5);
                    y <- (y0 - 5) to (y0 + 5)) yield (x, y)
    nbhd.sortBy({ case (x, y) => (x-x0)*(x-x0) + (y-y0)*(y-y0) })
        .flatMap(pt => canvasPtToSFSs(pt))
        .toVector
        .take(10)
  }

  // `factor` > 1 would zoom in
  def zoom(factor: Double = 1.05): Unit = {
    val xCenter = (xMin + xMax)/2
    val yCenter = (yMin + yMax)/2
    val xRadius = xMax - xCenter
    val yRadius = yMax - yCenter
    yMax = yCenter + yRadius / factor
    yMin = yCenter - yRadius / factor
    xMax = xCenter + xRadius / factor
    xMin = xCenter - xRadius / factor
    updateCanvas()
  }

  // Moves the canvas in direction specified by dir, by 0 < `percent` < 1 percent.
  def move(dir: (Double, Double), percent: Double): Unit = {
    val xCenter = (xMin + xMax)/2
    val yCenter = (yMin + yMax)/2
    val xRadius = xMax - xCenter
    val yRadius = yMax - yCenter
    val newXCenter = xCenter + dir._1 * percent
    val newYCenter = yCenter + dir._2 * percent
    yMax = newYCenter + yRadius
    yMin = newYCenter - yRadius
    xMax = newXCenter + xRadius
    xMin = newXCenter - xRadius
    updateCanvas()
  }


  def xyToCanvasCoord(pt: (Double, Double)): (Int, Int) = {
    val height = canvas.getHeight()
    val width = canvas.getWidth()
    val (x, y) = pt
    val canvasY = ((1.0 - (y - yMin) / (yMax - yMin)) * height).round.toInt
    val canvasX = ((x - xMin) / (xMax - xMin) * width).round.toInt
    (canvasX, canvasY)
  }

  def canvasCoordToXY(canvasX: Int, canvasY: Int): (Double, Double) = {
    val height = canvas.getHeight()*1.0
    val width = canvas.getWidth()*1.0
    val y = (1 - canvasY / height)*(yMax - yMin) + yMin
    val x = canvasX / width * (xMax - xMin) + xMin
    (x, y)
  }

  // `pt` is in canvas coordinates
  def isInCanvas(pt: (Int, Int)): Boolean = {
    val (x, y) = pt
    x >= 0 && y >= 0 && y < canvas.getHeight() && x < canvas.getWidth()
  }

  def fillOvalByCenter(x: Int, y: Int, diameter: Double): Unit = {
    gc.fillOval(x-diameter/2, y-diameter/2, diameter, diameter)
  }

  def fillPixel(canvasX: Int, canvasY: Int, color: Color): Unit = {
    gc.fill = color
    gc.fillRect(canvasX, canvasY, 1, 1)
  }

  def reset(color: Color): Unit = {
    gc.fill = color
    gc.fillRect(0, 0, canvas.width.get, canvas.height.get)
  }

  def updateCanvas2(): Unit = {
    val ptDiameter: Double =
      if (xMax - xMin > 2) 0.6
      else if (xMax - xMin > 1) 1.8
      else if (xMax - xMin > 0.5) 2.3
      else if (xMax - xMin > 0.25) 2.7
      else 5
    val canvasPtToSFSs = scala.collection.mutable.Map[(Int, Int), Vector[(RatPoint, Boolean)]]()
                            .withDefaultValue(Vector())

    reset(Color.rgb(0,0,0))

    gc.stroke = Color.WHITE
    val triVerts = Vector((0.0, 0.0), (math.sqrt(2), 0.0), (1.0/math.sqrt(2), math.sqrt(3.0/2.0)))
      .map(pt => xyToCanvasCoord(pt))
    
    triVerts.combinations(2).foreach { case Vector((x1, y1), (x2, y2)) => 
      gc.strokeLine(x1, y1, x2, y2)
    }

    def dist(r: RatPoint, pt: (Double, Double, Double)) = {
      val sq_dist = (1.0/r._1.toFloat - 1.0 / pt._1) * (1.0/r._1.toFloat - 1.0 / pt._1) +
      (1.0/r._2.toFloat - 1.0 / pt._2) * (1.0/r._2.toFloat - 1.0 / pt._2) +
      (1.0/r._3.toFloat - 1.0 / pt._3) * (1.0/r._3.toFloat - 1.0 / pt._3)
      math.sqrt(sq_dist)
    }

    val embPts = triData.embPts
    val nonEmbPts = triData.nonEmbPts
    val codims = triData.codims
    val minCodim = triData.codims.min
    val maxCodim = triData.codims.max
    val colors = Vector(Color.rgb(175, 220, 236),
      //Color.rgb(133, 187, 101),
      Color.rgb(230, 133, 101),
      Color.rgb(236, 220, 150)
      /*
      Color.rgb(150, 220, 236),
      Color.rgb(100, 220, 236),
      Color.rgb(90, 220, 236),
      Color.rgb(80, 220, 236),
      Color.rgb(70, 220, 236),
      Color.rgb(60, 220, 236),
      Color.rgb(50, 220, 236)
       */
    )

    for (canvasX <- 0 until canvas.getWidth().toInt;
      canvasY <- 0 until canvas.getHeight().toInt) {
      val (x_r2, y_r2) = canvasCoordToXY(canvasX, canvasY)
      if (canvasY == 0)
        println(canvasX)
      // Closest non-emb point
      val (x, y, z) = TriangleData.fromXY(x_r2, y_r2)
      val closestNonEmb = nonEmbPts
        .map({ nonEmbPt => (dist(nonEmbPt, (x,y,z)), nonEmbPt) })
        .minBy({ case (d, pt) => d })

      val closestEmb = (0 until embPts.length)
        .map({ i => (dist(embPts(i), (x,y,z)), embPts(i), codims(i)) })
        .minBy({ case (d, _, _) => d })

      val pixelColor = 
      if (closestNonEmb._1 < closestEmb._1) Color.rgb(0, 0, 0)
      else {
        val shade: Int = (closestEmb._3 - minCodim)
        if (shade >= colors.length) Color.rgb(255, 255, 255) else colors(shade)
      }
      fillPixel(canvasX, canvasY, pixelColor)
    }
    //this.canvasPtToSFSs = canvasPtToSFSs
  }


  def updateCanvas(): Unit = {
    val ptDiameter: Double =
      if (xMax - xMin > 2) 1.2
      else if (xMax - xMin > 1) 2.5
      else if (xMax - xMin > 0.5) 3.2
      else if (xMax - xMin > 0.25) 4.0
      else 5
    val canvasPtToSFSs = scala.collection.mutable.Map[(Int, Int), Vector[(RatPoint, Boolean)]]()
                            .withDefaultValue(Vector())

    reset(Color.rgb(0,0,0))
    //reset(Color.rgb(255,255,255))
    //reset(Color.rgb(150,150,200))
    //reset(Color.rgb(240,240,240))
    gc.stroke = Color.WHITE
    val triVerts = Vector((0.0, 0.0), (math.sqrt(2), 0.0), (1.0/math.sqrt(2), math.sqrt(3.0/2.0)))
      .map(pt => xyToCanvasCoord(pt))
    
    triVerts.combinations(2).foreach { case Vector((x1, y1), (x2, y2)) => 
      gc.strokeLine(x1, y1, x2, y2)
    }

    // Plot points with no lattice emb
    for (i <- 0 until triData.nonEmbPts.length) {
      val embeds = false
      val pt = triData.nonEmbPts(i)
      //gc.fill = Color.rgb(33,74,116) // non-emb color
      //gc.fill = Color.rgb(53,94,136) // non-emb color
      gc.fill = Color.rgb(0, 0, 0)
      val canvasPt = xyToCanvasCoord(TriangleData.toXY(pt))
      if (isInCanvas(canvasPt)) {
        canvasPtToSFSs(canvasPt) = (canvasPtToSFSs(canvasPt) :+ (pt, embeds)).distinct
        val (x, y) = canvasPt
        //gc.fillOval(x-1, y-1, 3, 3)
        fillOvalByCenter(x, y, ptDiameter)
      }
    }

    val minCodim = triData.codims.min
    val maxCodim = triData.codims.max
    println(s"Codim min/max: $minCodim, $maxCodim")

    val colors = Vector(Color.rgb(255, 0, 0),
      //Color.rgb(133, 187, 101),
      Color.rgb(  0, 255, 0),
      Color.rgb(0,   0, 255),
        
      Color.rgb(128, 255, 0),
      Color.rgb(0, 255, 0),
      Color.rgb(0, 255, 128),
      Color.rgb( 0, 255, 255),
      Color.rgb( 0, 128, 255),
      Color.rgb( 0,   0, 255),
      Color.rgb(255,   0, 255)
         
    )
    /*
    val colors = Vector(Color.rgb(175, 220, 236),
      
      Color.rgb(133, 187, 101),
      Color.rgb(236, 220, 150),
      Color.rgb(150, 220, 236),
      Color.rgb(100, 220, 236),
      Color.rgb(90, 220, 236),
      Color.rgb(80, 220, 236),
      Color.rgb(70, 220, 236),
      Color.rgb(60, 220, 236),
      Color.rgb(50, 220, 236)
    )*/

    // Plot points with lattice embeddings
    for (i <- 0 until triData.embPts.length) {
      val embeds = true
      val pt = triData.embPts(i)
      // shade is in [0, 1]
      //val shade: Double = (triData.codims(i) - minCodim) * 1.0 / (maxCodim - minCodim)
      //val grey = (shade*180).toInt
      val shade: Int = (triData.codims(i) - minCodim)

      if (shade >= colors.length) {
        gc.fill = Color.rgb(255, 255, 255)
        //gc.fill = Color.rgb(255, 50, 50) 
      } else {
        gc.fill = colors(shade)
      }

      val canvasPt = xyToCanvasCoord(TriangleData.toXY(pt))
      if (isInCanvas(canvasPt)) {
        canvasPtToSFSs(canvasPt) = (canvasPtToSFSs(canvasPt) :+ (pt, embeds)).distinct
        val (x, y) = canvasPt
        //gc.fillOval(x-1, y-1, 3, 3)
        fillOvalByCenter(x, y, ptDiameter)
      }
    }

    /*
    for ((pts, embeds) <- Vector((triData.embPts, true), (triData.nonEmbPts, false))) {
      //val fill = if (embeds) Color.rgb(0, 220, 0) else Color.rgb(180, 0, 0)
      val fill = if (embeds) Color.rgb(0, 0, 0) else Color.rgb(200, 200, 200)
      //val fill = if (embeds) Color.rgb(0, 140, 0) else Color.rgb(180, 0, 0)
      gc.fill = fill
      for (pt <- pts) {
        val canvasPt = xyToCanvasCoord(TriangleData.toXY(pt))
        if (isInCanvas(canvasPt)) {
          canvasPtToSFSs(canvasPt) = (canvasPtToSFSs(canvasPt) :+ (pt, embeds)).distinct
          val (x, y) = canvasPt
          //gc.fillOval(x-1, y-1, 3, 3)
          fillOvalByCenter(x, y, ptDiameter)
        }
      }
    }*/
    this.canvasPtToSFSs = canvasPtToSFSs
  }
}

object TriangleGUI {
  def saveCanvasAsImage(canvas: Canvas, filename: String): Unit = {
    import javafx.scene.image.WritableImage
    import javax.imageio.ImageIO
    import java.awt.image.RenderedImage
    import javafx.embed.swing.SwingFXUtils

    val file: File = new File(filename)
    val writableImage: WritableImage =
      new WritableImage(canvas.width.get.toInt, canvas.height.get.toInt);
    canvas.snapshot(null, writableImage);
    val renderedImage: RenderedImage = SwingFXUtils.fromFXImage(writableImage, null);
    ImageIO.write(renderedImage, "png", file);
  }

  def run(): Unit = {
    //val triData = TriangleData.loadFromFiles("has_emb_numer_80.txt", "no_emb_numer_80.txt")
    //val triData = TriangleData.loadFromFiles("3fib_40_has_emb.txt", "3fib_40_no_emb.txt")
    val triData = TriangleData.loadFromFiles("3fib_140_has_emb.txt", "3fib_120_no_emb.txt")
    //val triData = TriangleData.loadFromFiles("3fib_has_emb_100.txt", "3fib_no_emb_100.txt")
    val gui = new TriangleGUI(triData)
    gui.main(Array())
    sys.exit(0)
  }
}
