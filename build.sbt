
name := "JSAI"

version := "1.0"

scalaVersion := "2.12.8"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-language:postfixOps", "-language:implicitConversions")//, "-Xdisable-assertions")

// ScalaTest
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"

// ScalaCheck

resolvers ++= Seq(
  "snapshots" at "http://oss.sonatype.org/content/repositories/snapshots",
  "releases"  at "http://oss.sonatype.org/content/repositories/releases"
)

libraryDependencies ++= Seq(
  "org.scalacheck" %% "scalacheck" % "1.14.0" % "test"
)

// Disable parallel execution of tests
parallelExecution in Test := false

// show durations.
testOptions in Test ++= Seq(Tests.Argument("-oD"), Tests.Argument("-l"), Tests.Argument("Concrete"))

