// initial notJS state: Boolean

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


object InitBoolean {

  val Boolean_Obj = createFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr, "Boolean: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1, "Boolean: Arguments array refers to multiple addresses")

        val argsObj = σ.getObj(argArrayAddr.as.head)

        // use undefined in case of no arguments
        val input = argsObj(SConstNum("0")).getOrElse(Undef.BV)
        val in_bool = input.tobool
        // true iff invoking as a constructor
        val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
        /* If invoked as a constructor, selfAddr points to a Boolean object
           for us to populate; otherwise, we simply return the boolean value
           in_bool (not an object!) */
        if (calledAsConstr) {
          val check = (bv: BValue) ⇒
            assert(bv.defBool,
              "Boolean: in_bool should be a boolean; refactor valueObjConstructor")
          valueObjConstructor("Boolean")(check)(List(selfAddr, in_bool), x, ρ, σ, ß, κ, τ)
        } else makeState(in_bool, x, ρ, σ, ß, κ, τ)
      }
    ),
    ExternMap(exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(1)),
      SConstNotNum("prototype") → Address.inject(Boolean_prototype_Addr)
    ))
  )

  val Boolean_prototype_Obj = createObj(
    ExternMap(exactnotnum = Map(
      SConstNotNum("constructor") → Address.inject(Boolean_Addr),
      SConstNotNum("toString") → Address.inject(Boolean_prototype_toString_Addr),
      SConstNotNum("valueOf") → Address.inject(Boolean_prototype_valueOf_Addr)
    )),
    Map(
      Fields.classname → CBoolean,
      Fields.value → Bool.inject(BFalse)
    )
  ) // TODO: Special class, here and elsewhere

  val Boolean_prototype_toString_Obj =
    usualToPrim(_ == CBoolean, _.b.toStr, Str.⊥, Str.inject)(_ ⊔ _)

  val Boolean_prototype_valueOf_Obj =
    usualToPrim(_ == CBoolean, _.b, Bool.⊥, Bool.inject)(_ ⊔ _)
  
}
