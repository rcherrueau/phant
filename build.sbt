name := "phant"

version := "0.1"

// // For standard scala
scalaVersion := "2.11.5"

// Shows expansion of implicits:
// scalacOptions += "-Xlog-implicits"

scalacOptions += "-feature"

libraryDependencies += "org.spire-math" %% "spire" % "0.9.0"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.12.1"
