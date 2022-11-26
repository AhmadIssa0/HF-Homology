name := "hfhomology"
scalaVersion := "2.11.7"
libraryDependencies += "org.spire-math" %% "spire" % "0.11.0"
libraryDependencies += "org.scalafx" %% "scalafx" % "8.0.92-R10"
//libraryDependencies += "org.typelevel" %% "cats-core" % "1.0.1"

libraryDependencies ++= {
  // Determine OS version of JavaFX binaries
  lazy val osName = System.getProperty("os.name") match {
    case n if n.startsWith("Linux") => "linux"
    case n if n.startsWith("Mac") => "mac"
    case n if n.startsWith("Windows") => "win"
    case _ => throw new Exception("Unknown platform!")
  }
  Seq("base", "controls", "fxml", "graphics", "media", "swing", "web")
    .map(m => "org.openjfx" % s"javafx-$m" % "16" classifier osName)
}

javaOptions += "-Dfile.encoding=UTF-8"
// run chcp 65001 in command prompt
//javaOptions += "-Xprof"
fork := true
javaOptions += "-Xmx6G"
//scalaVersion := "2.11.7"


// Without the following line mathematica won't work. But SBT changed and no longer accepts <<=, need to fix.
//unmanagedBase <<= baseDirectory { base => file("C:/Program Files/Wolfram Research/Mathematica/10.0/SystemFiles/Links/JLink") }

cancelable in Global := true // allow ctrl+c in sbt to kill the forked jvm

// Allows us to use classes from another folder/project
//lazy val core = RootProject(file("../maths"))
//val main = Project(id = "application", base = file(".")).dependsOn(core) 

