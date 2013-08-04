// notJS initial state: Arguments

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Fields
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._


object InitArguments {

  // dummy arguments object used in several places:
  val Dummy_Arguments_Obj = Object(
    ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))),
    Map(
      Fields.proto → Address.inject(Object_prototype_Addr),
      Fields.classname → CArguments
    ),
    Set()
  )

  val Dummy_Obj = createObj()

  val Arguments_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      // TODO: assert called as constructor, explain
      // 
      makeState(selfAddr, x, ρ, σ, ß, κ, τ)
    }),
    external = ExternMap(
      exactnotnum = Map(
        SConstNotNum("prototype") → Address.inject(Object_prototype_Addr),
        SConstNotNum("length") → Num.inject(NConst(0)))))

}
