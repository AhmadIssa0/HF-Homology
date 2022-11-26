
package ahmad.hfhomology

import com.wolfram.jlink._

object Mathematica {
  val fileaddress = {
    import java.nio.file.{Paths, Files}
    val ver8 = "C:/Program Files/Wolfram Research/Mathematica/8.0/mathkernel.exe"
    val ver10 = "C:/Program Files/Wolfram Research/Mathematica/10.0/mathkernel.exe"
    if (Files.exists(Paths.get(ver8))) ver8 else ver10
  }
  val args: Array[String] = Array("-linkmode", "launch", "-linkname", "\"" + fileaddress + "\"")
  val ml = MathLinkFactory.createKernelLink(args)
  ml.discardAnswer()

  def evaluateToString(cmd: String): String = {
    // bug in JLink, if the output has length 127 it returns "", workaround:
    ml.evaluateToOutputForm(s"""s = ToString[InputForm[$cmd]]; If[StringLength[s] == 127, s <> " ", s]""", 0);
  }

  def graphToFile(adjacency: Matrix, filename: String): Unit = {
    val cmd =
      "Export[\"" + filename + "\", GraphPlot[AdjacencyGraph[" + adjacency +
        "], VertexLabeling -> True]];"
    evaluateToString(cmd)
  }
  
}
