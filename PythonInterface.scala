
package ahmad.hfhomology

import java.io._
import java.net._
import java.util._

object PythonInterface {

  val python = Runtime.getRuntime().exec("C:/Python27/python -i")
  val br = new BufferedReader(new InputStreamReader(python.getInputStream()))
  val bw = new BufferedWriter(new OutputStreamWriter(python.getOutputStream()))
  val berr = new BufferedReader(new InputStreamReader(python.getErrorStream()))
  discardInitialOutput()
  execute("import sys; sys.setrecursionlimit(10000)")

  private def discardInitialOutput(): Unit = {
    berr.read()
    read(berr)
  }


  def execute(cmd: String): Unit = {
    // blocks until finishes computation or detects error
    bw.write(cmd)
    bw.newLine()
    bw.flush()
    (0 until 4).foreach (_ => berr.read()) // python sends ">>> " to error stream once done processing
  }

  private def errors(): Option[String] = {
    // non-blocking
    read(berr) match {
      case "" => None
      case s => Some(s)
    }
  }

  def read(b: BufferedReader): String = {
    // non-blocking
    if (b.ready()) (b.read().toChar.toString + read(b))
    else ""
  }

  def readAll(b: BufferedReader): String = {
    // non-blocking
    if (b.ready()) (b.readLine + readAll(b))
    else ""
  }

  def command(cmd: String): Either[String, String] = {
    execute(cmd)
    errors() match {
      case None => Right(readAll(br))
      case Some(errorMsg) => Left(errorMsg)
    }
  }
}
