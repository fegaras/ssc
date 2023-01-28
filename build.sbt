name := "ssc"
organization := "edu.uta"
version := "0.1"
scalaVersion := "2.12.15"
licenses += "Apache-2.0" -> url("http://opensource.org/licenses/Apache-2.0")

libraryDependencies ++= Seq("org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2")

artifactName := { (sv: ScalaVersion, m: ModuleID, a: Artifact) => "../../lib/SSC.jar" }
