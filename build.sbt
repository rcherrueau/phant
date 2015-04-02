name := "phant"

version := "0.1"

// // For standard scala
scalaVersion := "2.11.6"

// Shows expansion of implicits:
// scalacOptions += "-Xlog-implicits"

// scalacOptions += "-Xprint:typer"

// scalacOptions += "-Ytyper-debug"

// scalacOptions += "-feature"

// // Import State from chap06
// unmanagedSourceDirectories in Compile +=
//   // file("/home/rl3x-desktop/prog/phant/src/main/scala")
//   file("/Users/rcherr12/prog/phant/src/main/scala")

libraryDependencies += "org.spire-math" %% "spire" % "0.9.0"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.12.1"

libraryDependencies +=  "com.chuusai" %% "shapeless" % "2.0.0"

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.1"

unmanagedJars in Compile ++=
  (file("utils/target/scala-2.11/") * "scala-illtyped_2.11-1.0.jar").classpath
