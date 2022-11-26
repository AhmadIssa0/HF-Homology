name := "hfhomology"

libraryDependencies += "org.spire-math" %% "spire" % "0.11.0"
libraryDependencies += "org.scalafx" %% "scalafx" % "8.0.92-R10"
//libraryDependencies += "org.typelevel" %% "cats-core" % "1.0.1"

javaOptions += "-Dfile.encoding=UTF-8"
// run chcp 65001 in command prompt
//javaOptions += "-Xprof"
fork := true
javaOptions += "-Xmx6G"
//scalaVersion := "2.11.7"
unmanagedBase <<= baseDirectory { base => file("C:/Program Files/Wolfram Research/Mathematica/10.0/SystemFiles/Links/JLink") }

cancelable in Global := true // allow ctrl+c in sbt to kill the forked jvm

// Allows us to use classes from another folder/project
//lazy val core = RootProject(file("../maths"))
//val main = Project(id = "application", base = file(".")).dependsOn(core) 

