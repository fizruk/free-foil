ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.12"

libraryDependencies += "org.antlr" % "antlr4" % "4.9.3"
libraryDependencies += "org.antlr" % "antlr4-runtime" % "4.9.3"

lazy val root = (project in file("."))
  .settings(
    name := "free-foil"
  )

lazy val runBNFCTask = TaskKey[Unit]("runBNFC", "Run BNF Converter to generate AST, parser, and printer")

runBNFCTask := {
  import sys.process._
  Seq("bnfc", "--java-antlr --makefile -p org.syntax.lambdapi grammar/LambdaPi/Simple.cf")
}

compile := ((Compile/compile) dependsOn runBNFCTask).value