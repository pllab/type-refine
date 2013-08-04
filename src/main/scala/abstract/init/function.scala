// notJS initial state: Function

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors
import notjs.abstracted.traces.Trace
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.interpreter.StatsDeux


object InitFunction {

  // creating the object explicitly because the prototype needs to be Object
  val Function_prototype_Obj = Object(
    ExternMap( exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(0)),
      SConstNotNum("apply") → Address.inject(Function_prototype_apply_Addr), // TODO
      SConstNotNum("call") → Address.inject(Function_prototype_call_Addr), // TODO
      SConstNotNum("toString") → Address.inject(Function_prototype_toString_Addr) // TODO
    ) ++ dangleMap(Map(
      SConstNotNum("constructor") → Address.inject(Function_Addr)))),
    Map(
      Fields.proto → Address.inject(Object_prototype_Addr),
      Fields.classname → CFunction_prototype_Obj,
      Fields.code → Set(Native(
        (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
          // TODO: if used as a constructor, throw a type error
          makeState(Undef.BV, x, ρ, σ, ß, κ, τ)
        }))
    ),
    Set(
      SConstNotNum("length"),
      SConstNotNum("constructor"),
      SConstNotNum("apply"),
      SConstNotNum("call"),
      SConstNotNum("toString")
    )
  )

  val Function_prototype_toString_Obj = constFunctionObj(ezSig(NoConversion, List()), Str.inject(STop))
 
  val Function_prototype_apply_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {

      assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses") 
      val argsObj = σ.getObj(argArrayAddr.as.head)

      val argLength = argsObj(SConstNotNum("length")).getOrElse(BValue.⊥).n
      assert(argLength != Num.⊥, "Arguments length is not a number!")

      // First, cast the first argument to object
      val input = argsObj(SConstNum("0")).getOrElse(Undef.BV)
      val traceAddr = τ.toAddr

      val (bv1, σ1, _) = toObjBody(input, σ, τ, traceAddr)

      val (σ2, bv2) = if (input.nil == MaybeNull || input.undef == MaybeUndef) {
         allocObj(Address.inject(Object_Addr), traceAddr, σ1, τ)
      } else (σ1, BValue.⊥)
      
      val newThisAddr = bv2 ⊔ bv1
      
      val extractedArgLength: Option[Int] = argLength match {
        case NConst(d) ⇒ Some(d.toInt)
        case _ ⇒ None
      }

      extractedArgLength match { // number of arguments passed to .apply
        case Some(2) ⇒ {
          // construct the new arguments object
          val newArgHolderAs_ = argsObj(SConstNum("1")).get
          val mightError = (!newArgHolderAs_.defAddr || !selfAddr.defAddr)// apply is a typeError if the second arg is not an object, or if 
                                                                           // the function is not definitely an address
          val newArgHolderAs = newArgHolderAs_.as

          val newArgLength = lookup(newArgHolderAs, SConstNotNum("length"), σ2).n
        
          if(newArgLength != Num.⊥) { //, "Apply arguments length is not a number!")

            val newExtractedArgLength: Option[Int] = newArgLength match {
              case NConst(d) ⇒ Some(d.toInt)
              case _ ⇒ None
            }
        
            val newArgsAddr = τ.modAddr(traceAddr, CArguments) 
            val intern = Map[Str,Any](Fields.proto → Address.inject(Object_prototype_Addr), Fields.classname → CArguments)
            val (num_, exactnum_, exactnotnum_) = newExtractedArgLength match {
              case Some(newlen) ⇒ {
                val num_ :Option[BValue] = None
                val exactnum_ = (0 until newlen).foldLeft(Map[SConstNum, BValue]())(
                  (acc, n) ⇒ (acc + (SConstNum(n.toString) → (lookup(newArgHolderAs, SConstNum(n.toString), σ2))))
                )
                val exactnotnum_ = Map[SConstNotNum, BValue](SConstNotNum("length") → Num.inject(NConst(newlen)))
                (num_, exactnum_, exactnotnum_)
              }
              case None ⇒ {
                val newlen = newArgLength
                val num_ :Option[BValue] = Option(lookup(newArgHolderAs, SNum, σ2))
                val exactnum_ = Map[SConstNum, BValue]()
                val exactnotnum_ = Map[SConstNotNum, BValue](SConstNotNum("length") → Num.inject(newlen))
                (num_, exactnum_, exactnotnum_)
              }
            }
            
            val newArgsObj = Object(ExternMap(num = num_, exactnotnum = exactnotnum_, exactnum = exactnum_), intern, Set(SConstNotNum("length")) ++ exactnum_.keys)
            val σ3 = σ2.alloc(newArgsAddr, newArgsObj)
            // Finally, apply.
            applyClo(selfAddr, newThisAddr, Address.inject(newArgsAddr), x, ρ, σ3, ß, κ, τ) ++ (if(mightError){StatsDeux.except(Trace.getBase(τ.toAddr), Errors.typeError); makeState(Errors.typeError, x, ρ, σ, ß, κ, τ)} else Set())
          } else {StatsDeux.except(Trace.getBase(τ.toAddr), Errors.typeError); makeState(Errors.typeError, x, ρ, σ, ß, κ, τ)}
        }

        case Some(1) ⇒ {
          // construct the new empty arguments object
            val newArgsAddr = τ.modAddr(traceAddr, CArguments) 
            val intern = Map[Str,Any](Fields.proto → Address.inject(Object_prototype_Addr), Fields.classname → CArguments)
            val newArgsObj = Object(
              ExternMap(
                exactnotnum = Map[SConstNotNum, BValue](SConstNotNum("length") → Num.inject(Num.Zero))), 
              intern, 
              Set(SConstNotNum("length")))
            val σ3 = σ2.alloc(newArgsAddr, newArgsObj)

            applyClo(selfAddr, newThisAddr, Address.inject(newArgsAddr), x, ρ, σ3, ß, κ, τ) ++ 
            (if(!selfAddr.defAddr){StatsDeux.except(Trace.getBase(τ.toAddr), Errors.typeError); makeState(Errors.typeError, x, ρ, σ, ß, κ, τ)} else Set())
          } 
        
        case x ⇒ sys.error("!! Not Implemented: .apply with arguments length = " + x)
      }
    }),
    ExternMap(exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(2))
  )))

  val Function_prototype_call_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses")
      val argsObj = σ.getObj(argArrayAddr.as.head)

      val argLength = argsObj(SConstNotNum("length")).getOrElse(BValue.⊥).n
      assert(argLength != Num.⊥, "Arguments length is not a number!")

      // First, cast the first argument to object
      val input = argsObj(SConstNum("0")).getOrElse(Undef.BV)
      val traceAddr = τ.toAddr
      
      val (bv1, σ1, _) = toObjBody(input, σ, τ, traceAddr)

      val (σ2, bv2) = if (input.nil == MaybeNull || input.undef == MaybeUndef) {
         allocObj(Address.inject(Object_Addr), traceAddr, σ1, τ)
      } else (σ1, BValue.⊥)
      
      val newThisAddr = bv2 ⊔ bv1

      val extractedArgLength: Option[Int] = argLength match {
        case NConst(d) ⇒ Some(d.toInt)
        case _ ⇒ None
      }
      
      val newArgsAddr = τ.modAddr(traceAddr, CArguments) // conflicts with newThisAddr, but different class, so it should be ok... TODO
      val intern = Map[Str,Any](Fields.proto → Address.inject(Object_prototype_Addr), Fields.classname → CArguments)
      val (num_, exactnum_, exactnotnum_) = extractedArgLength match {
        case Some(newlen) ⇒ {
          val num_ = None
          val exactnum_ = (1 until newlen).foldLeft(Map[SConstNum, BValue]())(
            (acc, n) ⇒ (acc + (SConstNum((n-1).toString) → (argsObj(SConstNum(n.toString)).get)))
            )
          val exactnotnum_ = Map[SConstNotNum, BValue](SConstNotNum("length") → Num.inject(NConst(newlen-1)))
          (num_, exactnum_, exactnotnum_)
        }
        case None ⇒ {
          val num_ = argsObj(SNum)
          val exactnum_ = Map[SConstNum, BValue]()
          // argLength is not a constant, so we can use it here
          val exactnotnum_ = Map[SConstNotNum, BValue](SConstNotNum("length") → Num.inject(argLength)) 
          (num_, exactnum_, exactnotnum_)
        }
      }
      val newArgsObj = Object(ExternMap(num = num_, exactnotnum = exactnotnum_, exactnum = exactnum_), intern, Set(SConstNotNum("length")) ++ exactnum_.keys)
    
      val σ3 = σ2.alloc(newArgsAddr, newArgsObj)
      // Finally, call.
      applyClo(selfAddr, newThisAddr, Address.inject(newArgsAddr), x, ρ, σ3, ß, κ, τ) ++ 
      (if(!selfAddr.defAddr){StatsDeux.except(Trace.getBase(τ.toAddr), Errors.typeError); makeState(Errors.typeError, x, ρ, σ, ß, κ, τ)} else Set())
    }
  ),
      ExternMap(exactnotnum = Map(
        SConstNotNum("length") → Num.inject(NConst(1))
      ))
    )
}
