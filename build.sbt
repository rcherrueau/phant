name := "phant"

version := "0.1"

// // For standard scala
scalaVersion := "2.11.5"

// Shows expansion of implicits:
scalacOptions += "-Xlog-implicits"

scalacOptions += "-feature"

// // For typelevel fork of scala
// scalaVersion := "2.11.2-typelevel"
//
// resolvers += Resolver.mavenLocal

// For nightly scala
// First, compile 2.12.0-nigthly:
// $ git clone git@github.com:scala/scala.git scala-2.12.0-nightly
// $ cd scala-2.12-0.nightly
// $ git checkout -b 2.12.x origin/2.12.x
// $ ant build-opt
// $ ant publish-local-opt -Dmaven.version.suffix="-nightly"
// $ # check the presence of 2.12.0-nightly in ~/.m2/repository/org/scala-*
// Then, in sbt with resolvers += Resolver.mavenLocal
// scalaVersion := "2.12.0-nightly"

libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value

// Not available for scala 2.12.0-nigthly
libraryDependencies +=  "com.chuusai" %% "shapeless" % "2.0.0"

libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.1" % "test"

unmanagedJars in Compile ++=
  (file("utils/target/scala-2.11/") * "scala-illtyped_2.11-1.0.jar").classpath
