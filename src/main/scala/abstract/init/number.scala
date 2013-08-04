// initial notJS state: Number

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.interpreter.StatsDeux


object InitNumber {

  val Internal_Number_constructor_afterToNumber = valueObjConstructor("Number") {
    arg_value ⇒ assert(arg_value.defNum,
      "Number constructor: type conversion ensures argument is a number")
  }
  val Internal_Number_normal_afterToNumber =
    (bvs: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(bvs.length == 1, "Number function: should have 1 argument by this point")
      val arg_value = bvs(0)
      assert(arg_value.defNum || arg_value.isBot, "Number function: type conversion ensures argument is a number" + arg_value)

      // if called as a function, merely convert argument to a number and return it
      makeState(arg_value, x, ρ, σ, ß, κ, τ)
    }
  val Number_Obj = createFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr, "Number: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1, "Number: Arguments array refers to multiple addresses")
        val argsObj = σ.getObj(argArrayAddr.as.head)

        // use 0 in case of no arguments
        val input = (argsObj(SConstNum("0")).getOrElse(Num.inject(Num.α(0))), NumberHint)

        // true iff invoking as a constructor
        val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
        val (convList, postConvF) =
          if (calledAsConstr)
            (List((selfAddr, NoConversion), input),
             Internal_Number_constructor_afterToNumber)
          else
            (List(input), Internal_Number_normal_afterToNumber)

        Convert(convList, postConvF, x, ρ, σ, ß, κ, τ)
      }
    ),
    ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Number_prototype_Addr),
      SConstNotNum("length") → Num.inject(NConst(1)),
      SConstNotNum("MAX_VALUE") → Num.inject(NReal), // TODO: Why are these not defined?
      SConstNotNum("MIN_VALUE") → Num.inject(NReal),
      SConstNotNum("NEGATIVE_INFINITY") → Num.inject(Num.NInf),
      SConstNotNum("POSITIVE_INFINITY") → Num.inject(Num.Inf)
    ), exactnum = Map(
      SConstNum("NaN") → Num.inject(Num.NaN)
    )), cls = CNumber_Obj
  )

  // TODO: We're not currently ever checking that someone might be misusing one of these as a constructor.
  val Number_prototype_Obj = createObj(ExternMap(exactnotnum = Map(
    SConstNotNum("constructor") → Address.inject(Number_Addr),
    SConstNotNum("toString") → Address.inject(Number_prototype_toString_Addr),
    SConstNotNum("valueOf") → Address.inject(Number_prototype_valueOf_Addr)
   ) ++ dangleMap(Map(
    SConstNotNum("toLocaleString") → Address.inject(Number_prototype_toLocaleString_Addr), // TODO
    SConstNotNum("toFixed") → Address.inject(Number_prototype_toFixed_Addr), // TODO
    SConstNotNum("toExponential") → Address.inject(Number_prototype_toExponential_Addr), // TODO
    SConstNotNum("toPrecision") → Address.inject(Number_prototype_toPrecision_Addr) // TODO
  ))),
    Map(
      Fields.classname → CNumber_prototype_Obj,
      Fields.value → Num.inject(Num.Zero))
  )

  val Internal_Number_prototype_toString_afterToNumber =
    (bvs: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(bvs.length == 2,
        "Number.prototype.toString: shoule have self value plus radix by this point")
      val List(selfNum, radix) = bvs
      assert(selfNum.defNum,
        "Number.prototype.toString: self value should be a number by this point")
      assert(radix.defNum,
        "Number.prototype.toString: radix should be a number by this point")

      /* give result for radix 10, STop for tricky but valid radix,
         and range error for invalid radix */
      val results: Set[Value] = radix.n match {
        case NBot ⇒ Set()
        case NConst(1) ⇒ Set(Str.inject(selfNum.n.toStr))
        case NConst(d) if (d >= 2 && d <= 36) ⇒ Set(Str.inject(STop))
        case NConst(_) ⇒ Set(rangeError)
        case _ ⇒ Set(Str.inject(STop), rangeError)
      }

      results flatMap { v ⇒ makeState(v, x, ρ, σ, ß, κ, τ) }
  }
  val Number_prototype_toString_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr,
          "Number.prototype.toString: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1,
          "Number.prototype.toString: Arguments array refers to multiple addresses")
        val argsObj = σ.getObj(argArrayAddr.as.head)

        /* NB: As far as I can tell the standard is ambiguous about whether to
           except from a non-numeric self or perform conversion of the radix first;
           I tried it out on V8 and SpiderMonkey and both seem to except first,
           so that's how it's implemented here.  If contrary engines are found
           and supporting them is desired, or this is otherwise deemed unsound,
           it may be necessary to choose the ordering nondeterministically. */

        val (selfNums, errs) =
          toPrimHelper(selfAddr, σ, isNumberClass, _.n, Num.⊥)(_ ⊔ _)

        /* optional argument: radix:
           if `undefined` or unspecified, default to 10 */
        val radix = argsObj(SConstNum("0")).getOrElse(Undef.BV)
        val radix_undef = Num.inject(if(radix.undef == MaybeUndef) NConst(10) else NBot)
        val radix_bv = radix_undef ⊔ radix

        val selfNum = selfNums.foldLeft[Num](Num.⊥)(_ ⊔ _)
        val numς =
          if (selfNum != Num.⊥)
            Convert(
              List((Num.inject(selfNum), NoConversion), (radix_bv, NumberHint)),
              Internal_Number_prototype_toString_afterToNumber,
              x, ρ, σ, ß, κ, τ)
          else Set()

        val errς = errs flatMap { v ⇒ StatsDeux.except(Trace.getBase(τ.toAddr), v); makeState(v, x, ρ, σ, ß, κ, τ) }

        numς ++ errς
      }
    ),
    ExternMap(exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(1))
    ))
  )

  val Number_prototype_valueOf_Obj =
    usualToPrim(isNumberClass, _.n, Num.⊥, Num.inject)(_ ⊔ _)

}
