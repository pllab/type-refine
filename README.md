# JSAI: JavaScript Abstract Interpreter

## Installation

In order to install and run the analysis, you will need:

1. [sbt version 0.12.1](http://www.scala-sbt.org/0.12.1/docs/home.html).
2. Scala version 2.10.1 (we need the new version of Scala, because the old version fails to compile our code, the new version of Scala has fixed the bug).
 
## Building

To build the project:

1. Do a clean
```console
$ sbt clean
```

2. Do a build
```console
$ sbt compile
```     

## Running

The different options to the abstract interpreter are given in `src/main/scala/abstract/interpreter.scala`. 

To run the abstract interpreter:

```console
$ sbt "run-main notjs.abstracted.interpreter.notJS <JavaScript file> <options>"
```
