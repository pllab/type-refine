// notJS init state: Typed Arrays

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.traces.Trace
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.init.Init._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Helpers._

object InitTypedArrays {

  val ArrayBuffer_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        // TODO: if not called as a constructor, throw a TypeError
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of ArrayBuffers with other objects")
        assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses")
        val argsObj = σ.getObj(argArrayAddr.as.head)
        val input = argsObj(SConstNum("0")).getOrElse(Num.inject(Num.Zero))
        // we should not throw an exception because selfAddr.defAddr
        val oldObj = (σ getObj selfAddr.as.head)
        // we join Num.Zero with Undef, because we don't know if the access will be within limits
        val updatedObj = Object(extern = ExternMap(num = Some(Num.inject(Num.Zero) ⊔ Undef.BV),
                                                   exactnotnum = Map(SConstNotNum("byteLength") → input)),
                                intern = oldObj.intern, present = oldObj.present + Str.α("byteLength"))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(ArrayBuffer_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.α(1)))))

    val Int8Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Int8Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Uint8Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Uint8Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Int16Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Int16Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Uint16Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Uint16Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Int32Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Int32Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Uint32Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Uint32Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Float32Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Float32Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Float64Array_Obj = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val oldObj = (σ getObj selfAddr.as.head)
        val updatedObj = Object(ExternMap(num = Some(Num.inject(NReal)),
                                          notnum = oldObj.extern.notnum,
                                          top = oldObj.extern.top,
                                          exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal))),
                                oldObj.intern,
                                Set(Fields.length))
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Float64Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val ArrayBuffer_prototype_Obj = createObj()

    val Int8Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Int8Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Int8Array_prototype_subarray_Addr))))

    val Uint8Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Uint8Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Uint8Array_prototype_subarray_Addr))))

    val Int16Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Int16Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Int16Array_prototype_subarray_Addr))))

    val Uint16Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Uint16Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Uint16Array_prototype_subarray_Addr))))

    val Int32Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Int32Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Int32Array_prototype_subarray_Addr))))

    val Uint32Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Uint32Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Uint32Array_prototype_subarray_Addr))))

    val Float32Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Float32Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Float32Array_prototype_subarray_Addr))))

    val Float64Array_prototype_Obj = createObj( ExternMap( exactnotnum = Map(
      SConstNotNum("set") → Address.inject(Float64Array_prototype_set_Addr),
      SConstNotNum("subarray") → Address.inject(Float64Array_prototype_subarray_Addr))))

    def createTypedArraySetFunction = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        makeState(Undef.BV, x, ρ, σ, ß, κ, τ)
      }), external = ExternMap(exactnotnum = Map(
        SConstNotNum("length") → Num.inject(Num.U32))))

    def createTypedArraySubarrayFunction(prototype: Address) = createFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
        val (σ1, subarrBV) = allocObj(Address.inject(Object_Addr), τ.toAddr, σ, τ)
        val oldObj = (σ1 getObj subarrBV.as.head)
        val updatedObj = oldObj copy (
          extern = (oldObj.extern copy (
            num = Some(Num.inject(NReal)), 
            exactnotnum = oldObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal)))),
          present = Set(Fields.length))
        makeState(subarrBV, x, ρ, σ1.putObj(subarrBV.as.head, updatedObj), ß, κ, τ)
      }
    ), external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(prototype),
      SConstNotNum("length") → Num.inject(Num.U32))))

    val Int8Array_prototype_set_Obj = createTypedArraySetFunction
    val Int8Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Int8Array_prototype_Addr)
    
    val Uint8Array_prototype_set_Obj = createTypedArraySetFunction
    val Uint8Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Uint8Array_prototype_Addr)

    val Int16Array_prototype_set_Obj = createTypedArraySetFunction
    val Int16Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Int16Array_prototype_Addr)

    val Uint16Array_prototype_set_Obj = createTypedArraySetFunction
    val Uint16Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Uint16Array_prototype_Addr)

    val Int32Array_prototype_set_Obj = createTypedArraySetFunction
    val Int32Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Int32Array_prototype_Addr)

    val Uint32Array_prototype_set_Obj = createTypedArraySetFunction
    val Uint32Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Uint32Array_prototype_Addr)

    val Float32Array_prototype_set_Obj = createTypedArraySetFunction
    val Float32Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Float32Array_prototype_Addr)

    val Float64Array_prototype_set_Obj = createTypedArraySetFunction
    val Float64Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Float64Array_prototype_Addr)
}