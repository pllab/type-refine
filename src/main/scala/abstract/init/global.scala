// initial notJS state: global object

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._


object InitGlobal {

  val window_Obj = createObj(ExternMap(exactnotnum = Map(
    SConstNotNum("window") → Address.inject(window_Addr),
    SConstNotNum("Arguments") → Address.inject(Arguments_Addr),
    SConstNotNum("undefined") → Undef.BV,
    SConstNotNum("decodeURI") → Address.inject(decodeURI_Addr),
    SConstNotNum("decodeURIComponent") → Address.inject(decodeURIComponent_Addr),
    SConstNotNum("encodeURI") → Address.inject(encodeURI_Addr),
    SConstNotNum("encodeURIComponent") → Address.inject(encodeURIComponent_Addr),
    SConstNotNum("escape") → Address.inject(escape_Addr),
    SConstNotNum("isFinite") → Address.inject(isFinite_Addr),
    SConstNotNum("isNaN") → Address.inject(isNaN_Addr),
    SConstNotNum("parseFloat") → Address.inject(parseFloat_Addr),
    SConstNotNum("parseInt") → Address.inject(parseInt_Addr),
    SConstNotNum("unescape") → Address.inject(unescape_Addr),
    SConstNotNum("Array") → Address.inject(Array_Addr),
    SConstNotNum("Boolean") → Address.inject(Boolean_Addr),
    SConstNotNum("Number") → Address.inject(Number_Addr),
    SConstNotNum("Object") → Address.inject(Object_Addr),
    SConstNotNum("String") → Address.inject(String_Addr),
    SConstNotNum("Date") → Address.inject(Date_Addr), // TODO
    SConstNotNum("JSON") → Address.inject(JSON_Addr), // TODO
    SConstNotNum("Math") → Address.inject(Math_Addr),
    SConstNotNum("RegExp") → Address.inject(RegExp_Addr),
    // typed array extensions
    SConstNotNum("ArrayBuffer") → Address.inject(ArrayBuffer_Addr), 
    SConstNotNum("Int8Array") → Address.inject(Int8Array_Addr), 
    SConstNotNum("Uint8Array") → Address.inject(Uint8Array_Addr), 
    SConstNotNum("Int16Array") → Address.inject(Int16Array_Addr), 
    SConstNotNum("Uint16Array") → Address.inject(Uint16Array_Addr), 
    SConstNotNum("Int32Array") → Address.inject(Int32Array_Addr), 
    SConstNotNum("Uint32Array") → Address.inject(Uint32Array_Addr), 
    SConstNotNum("Float32Array") → Address.inject(Float32Array_Addr), 
    SConstNotNum("Float64Array") → Address.inject(Float64Array_Addr), 
    // dummy address given so that arguments constructor can use them
    SConstNotNum("dummyAddress") → Address.inject(Dummy_Addr)
) ++ dangleMap(Map(
    SConstNotNum("Error") → Address.inject(Error_Addr), // TODO
    SConstNotNum("EvalError") → Address.inject(EvalError_Addr), // TODO
    SConstNotNum("RangeError") → Address.inject(RangeError_Addr), // TODO
    SConstNotNum("ReferenceError") → Address.inject(ReferenceError_Addr), // TODO
    SConstNotNum("TypeError") → Address.inject(TypeError_Addr), // TODO
    SConstNotNum("URIError") → Address.inject(URIError_Addr), // TODO
    SConstNotNum("Function") → Address.inject(Function_Addr) // TODO
  )), exactnum = Map(
    SConstNum("Infinity") → Num.inject(NConst(Double.PositiveInfinity)),
    SConstNum("NaN") → Num.inject(NConst(Double.NaN))
)))

  val uriMethodObj : Object =
    pureFunctionObj(ezSig(NoConversion, List(StringHint))) { _ ⇒
      Set(Str.inject(STop), uriError)
    }
  val decodeURI_Obj = uriMethodObj
  val decodeURIComponent_Obj = uriMethodObj
  val encodeURI_Obj = uriMethodObj
  val encodeURIComponent_Obj = uriMethodObj
  val compatabilityURIMethodObj : Object =
    constFunctionObj(ezSig(NoConversion, List(StringHint)),
      Str.inject(STop))
  val escape_Obj = compatabilityURIMethodObj
  val unescape_Obj = compatabilityURIMethodObj

  val isFinite_Obj = pureFunctionObj(ezSig(NoConversion, List(NumberHint))) {
    case List(_, bv) ⇒ {
      assert(bv.defNum, "isFinite: conversion should guarante argument must be a number")
      Set(Bool.inject(bv.n match {
        case NBot ⇒ BBot
        case NTop ⇒ BTop
        case NReal ⇒ BTrue
        case NConst(d) ⇒ d match {
          case Double.PositiveInfinity | Double.NegativeInfinity ⇒ BFalse
          case _ ⇒ if (d.isNaN) BFalse else BTrue
        }
      }))
    }
    case _ ⇒ sys.error("isFinite: signature conformance error")
  }
  val isNaN_Obj = pureFunctionObj(ezSig(NoConversion, List(NumberHint))) {
    case List(_, bv) ⇒ {
      assert(bv.defNum, "isNaN: conversion should guarantee argument must be a number")
      Set(Bool.inject(bv.n match {
        case NBot ⇒ BBot
        case NTop ⇒ BTop
        case NReal ⇒ BFalse
        case NConst(d) ⇒ if (d.isNaN) BTrue else BFalse
      }))
    }
    case _ ⇒ sys.error("isNaN: signature conformance error")
  }

  val parseFloat_Obj =
    constFunctionObj(ezSig(NoConversion, List(StringHint)), Num.inject(NTop))
  val parseInt_Obj =
    constFunctionObj(ezSig(NoConversion, List(StringHint, NumberHint)), Num.inject(NTop))

}
