// initial notJS state: Math

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._

object InitMath {

  val Math_Obj = createObj(ExternMap(exactnotnum = Map(
    // use NReal rather than an approximation, to be safe
    SConstNotNum("E") → Num.inject(NReal),
    SConstNotNum("LN10") → Num.inject(NReal),
    SConstNotNum("LN2") → Num.inject(NReal),
    SConstNotNum("LOG2E") → Num.inject(NReal),
    SConstNotNum("LOG10E") → Num.inject(NReal),
    SConstNotNum("PI") → Num.inject(NReal),
    SConstNotNum("SQRT1_2") → Num.inject(NReal),
    SConstNotNum("SQRT2") → Num.inject(NReal),
    SConstNotNum("abs") → Address.inject(Math_abs_Addr),
    SConstNotNum("acos") → Address.inject(Math_acos_Addr),
    SConstNotNum("asin") → Address.inject(Math_asin_Addr),
    SConstNotNum("atan") → Address.inject(Math_atan_Addr),
    SConstNotNum("atan2") → Address.inject(Math_atan2_Addr),
    SConstNotNum("ceil") → Address.inject(Math_ceil_Addr),
    SConstNotNum("cos") → Address.inject(Math_cos_Addr),
    SConstNotNum("exp") → Address.inject(Math_exp_Addr),
    SConstNotNum("floor") → Address.inject(Math_floor_Addr),
    SConstNotNum("log") → Address.inject(Math_log_Addr),
    SConstNotNum("max") → Address.inject(Math_max_Addr),
    SConstNotNum("min") → Address.inject(Math_min_Addr),
    SConstNotNum("pow") → Address.inject(Math_pow_Addr),
    SConstNotNum("random") → Address.inject(Math_random_Addr),
    SConstNotNum("round") → Address.inject(Math_round_Addr),
    SConstNotNum("sin") → Address.inject(Math_sin_Addr),
    SConstNotNum("sqrt") → Address.inject(Math_sqrt_Addr),
    SConstNotNum("tan") → Address.inject(Math_tan_Addr)
  )), internal = Map(Fields.classname → CMath_Obj))

  // Math functions don't convert self, and all arguments are numbers
  val unaryMathSig = ezSig(NoConversion, List(NumberHint))

  /* Some math functions send NTop to NTop, NReal to NReal,
     and have an easy Scala implementation with no requirement for approximation. */
  def easyMathFunctionObj(mathFun: Double ⇒ Double): Object =
    pureFunctionObj(unaryMathSig) {
      _ match {
        case List(_, bv) ⇒ {
          assert(bv.defNum, "type conversion should guarantee math functions only get nums")
          Set( Num.inject( bv.n match {
            case NConst(d) ⇒ NConst(mathFun(d))
            case num ⇒ num
          } ) )
        }
        case _ ⇒ sys.error("argument list to math function nonconformant to signature!")
      }
    }

  /* Others are not so easy!
     Math functions requiring machine-dependent approximation just return NTop;
     their edge cases tend to be machine-independent, but would likely not
     improve performance noticeably. */
  /* TODO: precision: some of these would send NReal to NReal
     with "reasonable assumptions" about machine approximations;
     maybe worth implementing (if assumptions prove correct) */
  val approxUnaryMathFunctionObj: Object =
    constFunctionObj(unaryMathSig, Num.inject(NTop))
  val approxBinaryMathFunctionObj: Object =
    constFunctionObj(ezSig(NoConversion, List(NumberHint, NumberHint)), Num.inject(NTop))

  val variadicMathFunctionObj: Object =
    constFunctionObj(VarSig(NoConversion, NumberHint, 2), Num.inject(NTop))

  val Math_abs_Obj = easyMathFunctionObj(_.abs)
  val Math_asin_Obj = approxUnaryMathFunctionObj
  val Math_atan_Obj = approxUnaryMathFunctionObj
  val Math_acos_Obj = approxUnaryMathFunctionObj
  val Math_atan2_Obj = approxBinaryMathFunctionObj
  val Math_ceil_Obj = easyMathFunctionObj(_.ceil)
  val Math_cos_Obj = approxUnaryMathFunctionObj
  val Math_exp_Obj = approxBinaryMathFunctionObj
  val Math_floor_Obj = easyMathFunctionObj(_.floor)
  val Math_log_Obj = approxUnaryMathFunctionObj
  val Math_max_Obj = variadicMathFunctionObj
  val Math_min_Obj = variadicMathFunctionObj
  val Math_pow_Obj = approxBinaryMathFunctionObj
  val Math_random_Obj = constFunctionObj(ezSig(NoConversion, List()), Num.inject(NReal))
  /* scala's round method does not match the JavaScript spec but it's still easy */
  val Math_round_Obj = easyMathFunctionObj { d ⇒ d match {
    case Double.PositiveInfinity ⇒ Double.PositiveInfinity
    case Double.NegativeInfinity ⇒ Double.NegativeInfinity
    case _ ⇒ if (d.isNaN) Double.NaN else d.round
  } }
  val Math_sin_Obj = approxUnaryMathFunctionObj
  val Math_sqrt_Obj = approxUnaryMathFunctionObj
  val Math_tan_Obj = approxUnaryMathFunctionObj

}
