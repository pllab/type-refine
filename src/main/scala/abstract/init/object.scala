// notJS initial state: Object

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._


object InitObject {

  val Object_Obj = createFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses")
        val argsObj = σ.getObj(argArrayAddr.as.head)
        // Note: Reading the sec, the constructor doesn't differ from the standard invocation except in the handling of 'host objects'.
        val input = argsObj(SConstNum("0")).getOrElse(Undef.BV)

        /* does not share exactly the behavior of toObj from the semantics
           document, but has much in common, captured in toObjBody */
        val resAddr = τ.toAddr
        val (bv1, σ1, _) = toObjBody(input, σ, τ, resAddr)

        val (σ2, bv2) = if (input.nil == MaybeNull || input.undef == MaybeUndef) {
           allocObj(Address.inject(Object_Addr), resAddr, σ1, τ)
        } else (σ1, BValue.⊥)

        makeState(bv2 ⊔ bv1, x, ρ, σ2, ß, κ, τ)
      }
    ),
    ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Object_prototype_Addr),
      SConstNotNum("length") → Num.inject(NConst(1))) ++ dangleMap(Map(
        SConstNotNum("create") → Address.inject(Object_create_Addr), // TODO
        SConstNotNum("defineProperties") → Address.inject(Object_defineProperties_Addr), // TODO
        SConstNotNum("defineProperty") → Address.inject(Object_defineProperty_Addr), // TODO
        SConstNotNum("freeze") → Address.inject(Object_freeze_Addr), // TODO
        SConstNotNum("getOwnPropertyDescriptor") → Address.inject(Object_getOwnPropertyDescriptor_Addr), // TODO
        SConstNotNum("getOwnPropertyNames") → Address.inject(Object_getOwnPropertyNames_Addr), // TODO
        SConstNotNum("getPrototypeOf") → Address.inject(Object_getPrototypeOf_Addr), // TODO
        SConstNotNum("isExtensible") → Address.inject(Object_isExtensible_Addr), // TODO
        SConstNotNum("isFrozen") → Address.inject(Object_isFrozen_Addr), // TODO
        SConstNotNum("isSealed") → Address.inject(Object_isSealed_Addr), // TODO
        SConstNotNum("keys") → Address.inject(Object_keys_Addr), // TODO
        SConstNotNum("preventExtensions") → Address.inject(Object_preventExtensions_Addr), // TODO
        SConstNotNum("seal") → Address.inject(Object_seal_Addr)
    ))), cls = CObject_Obj
  )

  val Object_prototype_Obj = createObj(ExternMap(exactnotnum = Map(
    SConstNotNum("constructor") → Address.inject(Object_Addr),
    SConstNotNum("toString") → Address.inject(Object_prototype_toString_Addr),
    SConstNotNum("toLocaleString") → Address.inject(Object_prototype_toLocaleString_Addr), // TODO
    SConstNotNum("valueOf") → Address.inject(Object_prototype_valueOf_Addr),
    SConstNotNum("hasOwnProperty") → Address.inject(Object_prototype_hasOwnProperty_Addr), // TODO
    SConstNotNum("isPrototypeOf") → Address.inject(Object_prototype_isPrototypeOf_Addr), // TODO
    SConstNotNum("propertyIsEnumerable") → Address.inject(Object_prototype_propertyIsEnumerable_Addr) // TODO
  )), Map(Fields.proto → Null.BV, Fields.classname → CObject_prototype_Obj))

  // TODO: can be more precise, when selfAddr is a single address.
  val Object_prototype_toString_Obj = constFunctionObj(
    ezSig(NoConversion, List()),
    Str.inject(SNotNum) )

  // TODO: this is a stopgap solution, come back to this
  val Object_prototype_toLocaleString_Obj = constFunctionObj(
    ezSig(NoConversion, List()),
    Str.inject(SNotNum) )

  val Object_prototype_hasOwnProperty_Obj = constFunctionObj(
    ezSig(NoConversion, List()),
    Bool.inject(BTop) )

  val Object_prototype_isPrototypeOf_Obj = constFunctionObj(
    ezSig(NoConversion, List()),
    Bool.inject(BTop) )

  val Object_prototype_propertyIsEnumerable_Obj = constFunctionObj(
    ezSig(NoConversion, List()),
    Bool.inject(BTop) )

  val Object_prototype_valueOf_Obj = pureFunctionObj(ezSig(NoConversion, List())) {
    case List(selfAddr) ⇒ Set(selfAddr)
    case _ ⇒ sys.error("Object.prototype.valueOf: signature nonconformance error")
  }

}
