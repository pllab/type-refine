// notJS initial state: Array-like objects

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.Init._
import notjs.abstracted.interpreter.StatsDeux


object InitArrays {

  val Array_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr, "Arguments array refers to non-addresses")
      assert(argArrayAddr.as.size == 1, "Arguments array refers to multiple addresses")

      val argsObj = σ.getObj(argArrayAddr.as.head)
      val argLength = argsObj(Fields.length).getOrElse(BValue.⊥).n
      assert(argLength != Num.⊥, "When constructing an array, arguments length should be provided")

      // true iff invoking as a constructor:
      val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
      /* Array behaves the same when called as a constructor and function,
         so the differences between the following codepaths are to compensate for the
         difference between method calls and constructor invocations in notJS. */
      val (σ1, arrayAddrs) = if (calledAsConstr) {
        // we should have already got an array allocated, the rest will be taken care of
        // by their respective constructor functions
        val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a).getJSClass == CArray)
        (σ, arrayAddrs)
      } else {
        // called as a function: first, construct the array object
        val (σ1, bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
        (σ1, bv.as)
      }
      assert(arrayAddrs.size == 1, "We should have allocated one and only one address for arrays")
      val arrayAddr = arrayAddrs.head
      val oldArrayObj = σ1 getObj arrayAddr

      val (argLenMaybe1, argLenMaybeNot1) = argLength match {
        case NConst(d) if (d.toInt == 1) ⇒ (true, false)
        case NConst(d) ⇒ (false, true)
        case _ ⇒ (true, true)
      }
      val extractedArgLength: Option[Int] = argLength match {
        case NConst(d) ⇒ Some(d.toInt)
        case _ ⇒ None
      }
      val arg0 = argsObj(SConstNum("0")).getOrElse(Undef.BV)
      val arg0MaybeNumeric = arg0.sorts(DNum)
      val arg0MaybeNotNumeric = !arg0.defNum

      /*    
         First, the "empty array with length set to a number" case should only
         apply when the singular argument is numeric (do not convert it);
         otherwise, a new array should be created as in the case of # of args
         not equal to one.
         Furthermore, the length property should be set to the argument provided,
         not the length of the arguments array. */

      val ones = if (argLenMaybe1 && arg0MaybeNumeric) {
        val (noexc, exc) = updateObj(Address.inject(arrayAddr), Str.inject(Fields.length), arg0.onlyNum, σ1)
        val s1 = noexc match {
          case Some((bv, σ2)) ⇒ {
            makeState(Address.inject(arrayAddr), x, ρ, σ2, ß, κ, τ)
          }
          case None ⇒ Set()
        }
        val s2 = exc match {
          case Some(ev) ⇒ makeState(ev, x, ρ, σ1, ß, κ, τ)
          case None ⇒ Set()
        }
        s1 ++ s2
      } else Set()

      val notones = if (argLenMaybeNot1 || arg0MaybeNotNumeric) {
        val updatedArrObj = extractedArgLength match {
          case Some(knownArgLength) ⇒ {
            Object(
              ExternMap(
                exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(knownArgLength))),
                exactnum = List.range(0, knownArgLength).foldLeft(Map[SConstNum, BValue]())((acc, e) ⇒ {
                  acc + (SConstNum(e.toString) → argsObj(SConstNum(e.toString)).getOrElse(Undef.BV))
                })
              ),
              oldArrayObj.intern,
              List.range(0, knownArgLength).map((i: Int) ⇒ Str.α(i.toString)).toSet + Fields.length
            )
          }
          case None ⇒ // arg length maybe 1, but it is not known exactly how much
            Object(
              // exactnotnum of argsObj is preserved because it has exactly the desired `length`
              // and no other properties
              ExternMap(num = argsObj.extern.num, exactnotnum = argsObj.extern.exactnotnum),
              oldArrayObj.intern,
              Set(Fields.length)
            )
        }
        makeState(Address.inject(arrayAddr), x, ρ, σ1.putObj(arrayAddr, updatedArrObj), ß, κ, τ)
      } else Set()

      ones ++ notones
    }),
    external = ExternMap(exactnotnum = Map(
      SConstNotNum("prototype") → Address.inject(Array_prototype_Addr),
      SConstNotNum("length") → Num.inject(NConst(1))) ++ dangleMap(Map(
      SConstNotNum("isArray") → Address.inject(Array_isArray_Addr)
      ))), cls = CArray_Obj
  )

  val Array_prototype_Obj = createObj(
    ExternMap(exactnotnum = Map(
      SConstNotNum("constructor") → Address.inject(Array_Addr),
      SConstNotNum("length") → Num.inject(Num.α(0)),
      SConstNotNum("concat") → Address.inject(Array_prototype_concat_Addr),
      SConstNotNum("indexOf") → Address.inject(Array_prototype_indexOf_Addr),
      SConstNotNum("join") → Address.inject(Array_prototype_join_Addr),
      SConstNotNum("lastIndexOf") → Address.inject(Array_prototype_lastIndexOf_Addr),
      SConstNotNum("pop") → Address.inject(Array_prototype_pop_Addr),
      SConstNotNum("push") → Address.inject(Array_prototype_push_Addr),
      SConstNotNum("reverse") → Address.inject(Array_prototype_reverse_Addr), // TODO
      SConstNotNum("shift") → Address.inject(Array_prototype_shift_Addr), // TODO
      SConstNotNum("sort") → Address.inject(Array_prototype_sort_Addr),
      SConstNotNum("splice") → Address.inject(Array_prototype_splice_Addr),
      SConstNotNum("toString") → Address.inject(Array_prototype_toString_Addr) // TODO
    ) ++ dangleMap(Map(
      SConstNotNum("every") → Address.inject(Array_prototype_every_Addr), // TODO
      SConstNotNum("filter") → Address.inject(Array_prototype_filter_Addr), // TODO
      SConstNotNum("forEach") → Address.inject(Array_prototype_forEach_Addr), // TODO
      SConstNotNum("map") → Address.inject(Array_prototype_map_Addr), // TODO
      SConstNotNum("reduce") → Address.inject(Array_prototype_reduce_Addr), // TODO
      SConstNotNum("reduceRight") → Address.inject(Array_prototype_reduceRight_Addr), // TODO
      SConstNotNum("slice") → Address.inject(Array_prototype_slice_Addr), // TODO
      SConstNotNum("some") → Address.inject(Array_prototype_some_Addr), // TODO
      SConstNotNum("toLocaleString") → Address.inject(Array_prototype_toLocaleString_Addr), // TODO
      SConstNotNum("unshift") → Address.inject(Array_prototype_unshift_Addr) // TODO
    ))),
    Map(Fields.classname → CArray_prototype_Obj)
  )

  val Array_prototype_join_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr, "Arguments array refers to non-addresses")
      assert(argArrayAddr.as.size == 1, "Arguments array refers to multiple addresses")
      val lenVal = lookup(selfAddr.as, Fields.length, σ)
      val argsObj = σ getObj argArrayAddr.as.head
      val separator = argsObj(SConstNum("0")) getOrElse Str.inject(Str.α(","))
      if (lenVal == Num.inject(NConst(0)))
        makeState(Str.inject(Str.α("")), x, ρ, σ, ß, κ, τ)
      else {
        val summaryVal = lookup(selfAddr.as, SNum, σ)
        ToString(List[BValue](separator, summaryVal), // call tostring on each of these
                (l: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
                  // then return STop
                  makeState(Str.inject(STop), x, ρ, σ, ß, κ, τ)
                }, x, ρ, σ, ß, κ, τ)
      }
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(1)))))

  val Array_prototype_pop_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      val lenVal = lookup(selfAddr.as, Fields.length, σ)

      // TODO: answer: can we assume `length` does not need type conversion?
      val zeroς = if (lenVal.n.defNot0) Set() else makeState(Undef.BV, x, ρ, σ, ß, κ, τ)

      // we choose to throw a type error if called on a non-array
      val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a).getJSClass == CArray)
      assert(arrayAddrs.size == 1, "We should have allocated one and only one address for arrays")
      val errς =
        if (arrayAddrs.size != selfAddr.as.size){
          StatsDeux.except(Trace.getBase(τ.toAddr), typeError);
          makeState(typeError, x, ρ, σ, ß, κ, τ)
        }
        else
          Set()

      val arrayAddr = arrayAddrs.head
      val oldArrayObj = σ getObj arrayAddr
      // TODO: precision if length known?
      val summaryVal = lookup(arrayAddrs, SNum, σ)
      val updatedArrObj = oldArrayObj copy (
        extern = oldArrayObj.extern copy (
          exactnotnum = oldArrayObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal)),
          num = Some(summaryVal)
        ),
        present = Set(Fields.length)
      )
      val nonzeroς =
        if (lenVal.n.def0)
          Set()
        else
          makeState(summaryVal, x, ρ, σ.putObj(arrayAddr, updatedArrObj), ß, κ, τ)

      zeroς ++ nonzeroς ++ errς
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_push_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr,
        "Array.prototype.push: Arguments array should refer to addresses")
      assert(argArrayAddr.as.size == 1,
        "Array.prototype.push: Arguments array should refer to a single address")

      // we choose to throw a type error if called on a non-array
      /* TODO: if this sort of thing is a common pattern, factor it out
         into a helper */
      /* TODO: additionally, check if we care about anything which has
         non-TypeError behavior, and if so, account for that. */
      val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a).getJSClass == CArray)
      val errς =
        if (arrayAddrs.size != selfAddr.as.size) {
          StatsDeux.except(Trace.getBase(τ.toAddr), typeError);
          makeState(typeError, x, ρ, σ, ß, κ, τ)
        }
        else
          Set()

      val isStrong = arrayAddrs.size == 1 && σ.isStrong(arrayAddrs.head)    
      val σ1 = arrayAddrs.foldLeft(σ) {
        case (acc, arrayAddr) ⇒ {
          val oldArrayObj = acc getObj arrayAddr
          // TODO: precision if length known?
          val summaryVal = lookup(Addresses(arrayAddr), SNum, acc) ⊔ lookup(argArrayAddr.as, SNum, acc)
          val updatedArrObj = oldArrayObj copy (
            extern = oldArrayObj.extern copy (
              exactnotnum = oldArrayObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal)),
              num = Some(summaryVal)
            ),
            present = Set(Fields.length)
          )
          if (isStrong)
            acc.putObjStrong(arrayAddr, updatedArrObj)
          else   
            acc.putObjWeak(arrayAddr, updatedArrObj)
        }
      }    
      val pushedς = makeState(Num.inject(NReal), x, ρ, σ1, ß, κ, τ)

      pushedς ++ errς
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(1)))))

  val Array_prototype_indexOf_Obj =
    constFunctionObj(Sig(NoConversion, List(NoConversion, NumberHint), 1), Num.inject(NReal))
  val Array_prototype_lastIndexOf_Obj =
    constFunctionObj(Sig(NoConversion, List(NoConversion, NumberHint), 1), Num.inject(NReal))

  /* concatenate self with all provided arguments,
     treating non-arrays as singletons */
  val Array_prototype_concat_Obj = createFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr,
          "Array.prototype.concat: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1,
          "Array.prototype.concat: Arguments array refers to multiple addresses")
        val argsArray = σ getObj argArrayAddr.as.head

        val argsSummary = selfAddr ⊔ argsArray(SNum).getOrElse(BValue.⊥)
        /* compute summary of new entries by joining all entries of array arguments
           with all non-array arguments */
        val (arrayAddrs, nonArrayAddrs) = argsSummary.as partition {
          a ⇒ σ.getObj(a).getJSClass == CArray
        }
        val entrySummary = argsSummary.copy(as = nonArrayAddrs) ⊔ lookup(arrayAddrs, SNum, σ)

        /* allocate new array to house summary */
        val (σ1, resaddr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
        assert(resaddr_bv.as.size == 1,
          "Array.prototype.concat: freshly allocated address set should be singleton")
        val resaddr = resaddr_bv.as.head
        val oldArrayObj = σ1 getObj resaddr

        val resArray = oldArrayObj copy (
          extern = oldArrayObj.extern copy (
            exactnotnum = Map(SConstNotNum("length") → Num.inject(NReal)),
            num = Some(entrySummary)
          ),
          present = Set(Fields.length)
        )

        makeState(resaddr_bv, x, ρ, σ1.putObj(resaddr, resArray), ß, κ, τ)
      }
    ),
    external = ExternMap(exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(1))
    ))
  )

  /* returns new array where all entries are a summary value containing the join
     of all of self's entries */
  val Array_prototype_sort_Obj = createFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        // we choose to throw a type error if called on a non-array
        /* TODO: if this sort of thing is a common pattern, factor it out
           into a helper */
        /* TODO: additionally, check if we care about anything which has
           non-TypeError behavior, and if so, account for that. */
        val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a).getJSClass == CArray)
        assert(arrayAddrs.size == 1,
          "We should have allocated one and only one address for arrays")
        val errς =
          if (arrayAddrs.size != selfAddr.as.size){
            StatsDeux.except(Trace.getBase(τ.toAddr), typeError);
            makeState(typeError, x, ρ, σ, ß, κ, τ)
          }
          else
            Set()
        val arrayAddr = arrayAddrs.head

        val selfArray = σ getObj arrayAddr
        val entrySummary = selfArray(SNum) getOrElse Undef.BV

        /* allocate new array to house summary */
        val (σ1, resaddr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
        assert(resaddr_bv.as.size == 1,
          "Array.prototype.concat: freshly allocated address set should be singleton")
        val resaddr = resaddr_bv.as.head
        val freshObj = σ1 getObj resaddr

        val resArray = freshObj copy (
          extern = freshObj.extern copy (
            /* exactnotnum of selfArray is preserved because it has exactly the desired `length`
               and no other properties */
            exactnotnum = selfArray.extern.exactnotnum,
            num = Some(entrySummary)
          ),
          present = Set(Fields.length)
        )

        errς ++ makeState(resaddr_bv, x, ρ, σ1.putObj(resaddr, resArray), ß, κ, τ)
      }
    ),
    external = ExternMap(exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(1))
    ))
  )

  /* splice: concretely, takes a start index, number of items to replace, and replacements therefor,
     then modifies self to perform replacement and returns an array of deleted entries.
     abstractly, return new array with all entries being the join of all of self's,
     and modify self such that all of its entries are a summary of its old entries,
     joined with a summary of all replacement arguments */
  val Array_prototype_splice_Obj = createFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr,
          "Array.prototype.concat: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1,
          "Array.prototype.concat: Arguments array refers to multiple addresses")
        val argArray = σ getObj argArrayAddr.as.head

        // we choose to throw a type error if called on a non-array
        /* TODO: if this sort of thing is a common pattern, factor it out
           into a helper */
        /* TODO: additionally, check if we care about anything which has
           non-TypeError behavior, and if so, account for that. */
        val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a).getJSClass == CArray)
        assert(arrayAddrs.size == 1,
          "We should have allocated one and only one address for arrays")
        val errς =
          if (arrayAddrs.size != selfAddr.as.size){
            StatsDeux.except(Trace.getBase(τ.toAddr), typeError)
            makeState(typeError, x, ρ, σ, ß, κ, τ)
          }
          else
            Set()
        val selfArrayAddr = arrayAddrs.head

        val oldSelf = σ getObj selfArrayAddr
        val oldSummary = oldSelf(SNum) getOrElse Undef.BV
        val newSummary = oldSummary ⊔ argArray(SNum).getOrElse(BValue.⊥)

        /* update self with summary including arguments */
        val newSelf = oldSelf copy (
          extern = oldSelf.extern copy (
            exactnotnum = oldSelf.extern.exactnotnum ++ Map(SConstNotNum("length") → Num.inject(NReal)),
            num = Some(newSummary)
          )
        )
        val σ1 = σ.putObj(selfArrayAddr, newSelf)

        /* allocate return array */
        val (σ2, retAddr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ1, τ)
        assert(retAddr_bv.as.size == 1,
          "Array.prototype.concat: freshly allocated address set should be singleton")
        val retAddr = retAddr_bv.as.head
        val freshObj = σ2 getObj retAddr
        /* populate return array with summary of original array */
        val retArray = freshObj copy (
          extern = freshObj.extern copy (
            exactnotnum = Map(SConstNotNum("length") → Num.inject(NReal)),
            num = Some(oldSummary)
          ),
          present = Set(Fields.length)
        )
        val σ3 = σ2.putObj(retAddr, retArray)

        errς ++ makeState(retAddr_bv, x, ρ, σ3, ß, κ, τ)
      }
    ),
    external = ExternMap(exactnotnum = Map(
      SConstNotNum("length") → Num.inject(NConst(2))
    ))
  )

  val Array_prototype_every_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.every: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_filter_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.filter: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_forEach_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.forEach: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_map_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.map: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_reduce_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.reduce: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_reduceRight_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.reduceRight: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_reverse_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      // we choose to throw a type error if called on a non-array
      val arrayAddrs = selfAddr.as.collect({case a if σ.getObj(a).getJSClass == CArray ⇒ a})
      assert(arrayAddrs.size == 1, "We should have allocated one and only one address for arrays")
      val arrayAddr = arrayAddrs.head
      val oldArrayObj = σ getObj arrayAddr
      val summaryVal = lookup(arrayAddrs, SNum, σ)
      val updatedArrObj = oldArrayObj copy (
        extern = oldArrayObj.extern.copy(
          num = Some(summaryVal)
          )
        )
      makeState(Addresses.inject(arrayAddrs), x, ρ, σ.putObj(arrayAddr, updatedArrObj), ß, κ, τ) ++
      (if (arrayAddrs.size != selfAddr.as.size){
        StatsDeux.except(Trace.getBase(τ.toAddr), typeError)
        makeState(typeError, x, ρ, σ, ß, κ, τ)
      }
       else Set())
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_shift_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        // we choose to throw a type error if called on a non-array
      val arrayAddrs = selfAddr.as.collect({case a if σ.getObj(a).getJSClass == CArray ⇒ a})
      assert(arrayAddrs.size == 1, "We should have allocated one and only one address for arrays")
      val arrayAddr = arrayAddrs.head
      val oldArrayObj = σ getObj arrayAddr
      val summaryVal = lookup(arrayAddrs, SNum, σ)
      val updatedArrObj = oldArrayObj copy (
        extern = oldArrayObj.extern.copy(
          exactnotnum = oldArrayObj.extern.exactnotnum + (SConstNotNum("length") → Num.inject(NReal)),
          num = Some(summaryVal)
      ))
      makeState(summaryVal, x, ρ, σ.putObj(arrayAddr, updatedArrObj), ß, κ, τ) ++
      (if (arrayAddrs.size != selfAddr.as.size){
        StatsDeux.except(Trace.getBase(τ.toAddr), typeError)
        makeState(typeError, x, ρ, σ, ß, κ, τ)
      }
       else Set())
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_slice_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.slice: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_some_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.some: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_toLocaleString_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.toLocaleString: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_toString_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      // ECMA spec
      // 1. Let array be the result of calling ToObject on the this value.
      // 2. Let func be the result of calling the [[Get]] internal method of array with argument "join".
      // 3. If IsCallable(func) is false, then let func be the standard built-in method Object.prototype.toString (15.2.4.2).
      // 4. Return the result of calling the [[Call]] internal method of func providing array as the this value and an empty arguments list.
      val func = lookup(selfAddr.as, Str.α("join"), σ)
      val callableAddrs = func.as.filter(a ⇒ σ.getObj(a).getCode.nonEmpty) - Array_prototype_toString_Addr
      
      // since all such addrs here are callable, we will never raise an exception from apply clo
      applyClo(Addresses.inject(callableAddrs), selfAddr, Address.inject(Dummy_Arguments_Addr), x, ρ, σ, ß, κ, τ) ++
      (if (!func.defAddr || (callableAddrs.size != func.as.size)) // possible non-function "join"s
        applyClo(Address.inject(Object_prototype_toString_Addr), selfAddr, Address.inject(Dummy_Arguments_Addr), x, ρ, σ, ß, κ, τ)
       else Set()
      ) ++ 
      (if (!func.defAddr) {
        StatsDeux.except(x.id, typeError); Set(notjs.abstracted.interpreter.State(typeError, ρ, σ, ß, κ, τ))
        } else Set()
      )    
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

  val Array_prototype_unshift_Obj = createFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error("Array.unshift: Not implemented")
    }
  ), external = ExternMap(exactnotnum = Map(SConstNotNum("length") → Num.inject(NConst(0)))))

}
