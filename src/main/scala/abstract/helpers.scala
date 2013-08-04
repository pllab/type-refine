// This file contains the definitions of the abstract helper
// functions. See the notJS semantics document Section 3.5 for the
// specifications.

package notjs.abstracted.helpers

import notjs.syntax._
import notjs.abstracted.init.Init._
import notjs.abstracted.traces._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.interpreter._

import scala.collection.mutable.{ HashMap }

//——————————————————————————————————————————————————————————————————————————————
// handy definitions

// exceptions that can be thrown implicitly
object Errors {
  val typeError   = EValue(Str.inject(Str.α("TypeError")))
  val rangeError  = EValue(Str.inject(Str.α("RangeError")))
  val uriError    = EValue(Str.inject(Str.α("URIError")))
  val syntaxError = EValue(Str.inject(Str.α("SyntaxError")))
}

object Filters {

    // helper class for value refinement
  // specifies which fields should be intersected/subtraced
  sealed abstract class BVFilter
  case object BooleanFilter extends BVFilter
  case object ToBoolFilter extends BVFilter
  case object TypeofNumFilter extends BVFilter
  case object TypeofBoolFilter extends BVFilter
  case object TypeofStrFilter extends BVFilter
  case object TypeofObjFilter extends BVFilter
  case object TypeofUndefFilter extends BVFilter
  case object FuncFilter extends BVFilter
  case object UndefNullFilter extends BVFilter
  case object ToPrimFilter extends BVFilter
  case object IdentityFilter extends BVFilter //unused

}
// builtin object fields
object Fields {
  val proto       = Str.α("proto")
  val classname   = Str.α("class")
  val code        = Str.α("code")
  val prototype   = Str.α("prototype")
  val length      = Str.α("length")
  val value       = Str.α("value")
  val message     = Str.α("message")
  val constructor = Str.α("constructor")
}

import Errors._
import Fields._
import Filters._

//——————————————————————————————————————————————————————————————————————————————
// helper functions

object Helpers {



  // check if an expression is a variable or a string access
  def refineable(e:Exp):Boolean = e match {
    case v:Var ⇒ true
    case Binop(⌜⋆⌝, _, _) ⇒ true
    case _ ⇒ false
  }







  // compute refinement filter based on input expression, return filter and 
  // simple expression to refine upon
  def getFilter(e:Exp):Option[(BVFilter, Exp)] = {

    // package an expression up with a filter in an option, if the expression is
    // refineable
    def refineableWithFilter(fil:BVFilter, eInner:Exp):Option[(BVFilter, Exp)] = {
      if (refineable(eInner))
        Some(fil, eInner)
      else
        None
    }


    def typeofExtractor(b:Binop):Option[(Exp, String)] = b match {
      case Binop(⌜≈⌝, Unop(Typeof, ein), StrAST(s)) ⇒ Some(ein, s)
      case Binop(⌜≈⌝, StrAST(s), Unop(Typeof, ein)) ⇒ Some(ein, s)
      case Binop(⌜≡⌝, Unop(Typeof, ein), StrAST(s)) ⇒ Some(ein, s)
      case Binop(⌜≡⌝, StrAST(s), Unop(Typeof, ein)) ⇒ Some(ein, s)
      case _ ⇒ None
    }

    // first check if we should do boolean refinement,
    // then check other types of refinement
    // return None if we syntactically cannot perform refinement
    refineableWithFilter(BooleanFilter, e) match {
      case res@Some(_) ⇒ res
      case None ⇒ e match {
        case b:Binop ⇒ typeofExtractor(b) match {
            case Some((ein, s)) ⇒ s match {
              case "number" ⇒ refineableWithFilter(TypeofNumFilter, ein)
              case "boolean" ⇒ refineableWithFilter(TypeofBoolFilter, ein)
              case "string" ⇒ refineableWithFilter(TypeofStrFilter, ein)
              case "object" ⇒ refineableWithFilter(TypeofObjFilter, ein) 
              case "undefined" ⇒ refineableWithFilter(TypeofUndefFilter, ein)
              case "function" ⇒ refineableWithFilter(FuncFilter, ein)
              case _ ⇒ None
            }
            case _ ⇒ None
          }        

        case Unop(IsPrim, ein) ⇒ refineableWithFilter(ToPrimFilter, ein)
        case Unop(ToBool, ein) ⇒ refineableWithFilter(ToBoolFilter, ein)

        case _ ⇒ None
      }
    }
  }


  // perform conditional branch refinement on given store and scratchpad
  // for a given expression e.
  // return (σT, ßT, σF, ßF)

  def branchRefine(e:Exp, σ:Store, ρ:Env, ß:Scratchpad) = getFilter(e) match {
    case Some((bvf, ein)) ⇒ refine(bvf, ein, σ, ρ, ß)
    case _ ⇒ (σ, ß, σ, ß)
  }


  // perform execution branch refinement on given store and scratchpad,
  // for a given expression e.
  // return store and scratchpad for non-exceptional branch

  def excRefine(e:Exp, σ:Store, ρ:Env, ß:Scratchpad, bvf:BVFilter) = {
    if (refineable(e)) {
      val res = refine(bvf, e, σ, ρ, ß)
      (res._1, res._2)
    } else {
      (σ, ß)
    }
  }

  // driver function for refinement
  // given input simple expression, store, scratchpad, and filter, 
  // return refined stores and scratchpads, in format
  // (σT, ßT, σF, ßF)

  def refine(bvf:BVFilter, e:Exp, σ:Store, ρ:Env, ß:Scratchpad) = e match {
    case x:PVar ⇒ 
      // if it is a single address (strong)
      val as = ρ(x)
      if (as.size == 1) {
        val (newBVT, newBVF) = σ(as).filterBy(bvf, σ)
        (σ + (as → newBVT), ß, σ + (as → newBVF), ß)
      } else (σ, ß, σ, ß)
    
    case x:Scratch ⇒ 
      val (newBVT, newBVF) = ß(x).filterBy(bvf, σ)
      (σ,ß(x) = newBVT, σ, ß(x) = newBVF)
    

    case Binop(⌜⋆⌝, el, er) ⇒ 
      import notjs.abstracted.eval.Eval
      val objbv = Eval.eval(el, ρ, σ, ß )
      val strbv = Eval.eval(er, ρ, σ, ß )
      refineLookup(objbv, strbv.str, σ) match {
        case Some((addr, o)) ⇒ {
          val oldBV = o(strbv.str) match {
            case Some(bv) ⇒ bv
            case _ ⇒ sys.error("refineLookup returned bad object")
          }
          // create the new BV
          val (newBVT, newBVF) = oldBV.filterBy(bvf, σ)
          // create the new objects
          val oT = o copy (extern = o.extern ++ (strbv.str -> newBVT))
          val σT = σ.putObjStrong(addr, oT)    
          val oF = o copy (extern = o.extern ++ (strbv.str -> newBVF))
          val σF = σ.putObjStrong(addr, oF)    
          (σT, ß, σF, ß)
        }
        case None ⇒ (σ, ß, σ, ß)
      }

      case _ ⇒ // probably should not have gotten here
        sys.error("bad input to refine")     
    
  }


  // helper function for value refinement
  // given base value for object in refinement, 
  // check if refinement is doable. if doable, return (address, object) for object
  // that will receive refinement. if not doable, return None
  def refineLookup( bv:BValue, str:Str, σ:Store ): Option[(Address, Object)] = {
    // we can refine iff 
    // 0: str is exact
    // 1: bv points to a single address
    // 2: bv.a is strong
    if ((bv.as.size == 1) && (σ.isStrong(bv.as.head)) && (Str.isExact(str))) {
      val obj = σ.getObj(bv.as.head)
      // 3: the object pointed to by a definitely contains str 
      if (obj.defField(str)) Some(bv.as.head, obj)
      // else if definitely not a field on this obj lookup prototype chain
      else if (obj.defNotField(str)) refineLookup(obj.getProto, str, σ)
      // otherwise, we cannot refine, the field may be present on this obj
      else None
      
    } else None // we cannot do refinement
  }

  // // refine scratchpad or store based on given expression, for excecutions
  // // if calls is true, the refinement retains only addresses
  // // else it removes undef and null
  // // return (storeNonExc, scratchpadNonExc)
  // def excRef(τ:Trace, e:Exp, σ:Store, ß:Scratchpad, ρ:Env, isCall: Boolean = false) = e match {
  //   case x:PVar ⇒ {
  //     if (notJS.Mutable.stats) {Stats.nondetExc(τ, true)}
  //     // if it is a single address
  //     val as = ρ(x)
  //     if (as.size == 1) {
  //       val oldBV = σ(as)
  //       val newBV = if (isCall) oldBV.onlyAddr else oldBV.removeNullAndUndef
  //       (σ + (as → newBV), ß)
  //     } else (σ, ß)
  //   }
  //   case x:Scratch ⇒ {
  //     if (notJS.Mutable.stats) {Stats.nondetExc(τ, true)}
  //     val oldBV = ß(x)
  //     val newBV = if (isCall) oldBV.onlyAddr else oldBV.removeNullAndUndef
  //     (σ,ß(x) = newBV)
  //   }

  //   case Binop(⌜⋆⌝, el, er) ⇒ {
  //     if (notJS.Mutable.stats) {Stats.nondetExc(τ, true)}
  //     import notjs.abstracted.eval.Eval
  //     val objbv = Eval.eval(el, ρ, σ, ß )
  //     val strbv = Eval.eval(er, ρ, σ, ß )
  //     refineLookup(objbv, strbv.str, σ) match {
  //       case Some((addr, o)) ⇒ {
  //         val oldBV = o(strbv.str) match {
  //           case Some(bv) ⇒ bv
  //           case _ ⇒ sys.error("refineLookup returned bad object")
  //         }
  //         // create the new BV
  //         val newBV = if (isCall) oldBV.onlyAddr else oldBV.removeNullAndUndef
  //         // create the new objects
  //         val _o = o copy (extern = o.extern ++ (strbv.str -> newBV))
  //         val _σ = σ.putObjStrong(addr, _o)    
  //         (_σ,ß)
  //       }
  //       case None ⇒ (σ,ß)
  //     }     
  //   }

  //   case _ ⇒ {
  //     if (notJS.Mutable.stats) {Stats.nondetExc(τ, false)}
  //     (σ,ß)
  //   }
  // }

  // // refine scratchpad or store based on given expression, for function calls (ie, entry to applyClo)
  // // return (storeFunction, scratchpadFunction)
  // def funcRef(τ:Trace, e:Exp, σ:Store, ß:Scratchpad, ρ:Env) = 
  //   excRef(τ, e, σ, ß, ρ, true)




  // // return refined basevalues for true and false branch
  // // for a typeof x == string, x → bv
  // def refTypeof(bv:BValue, s:String, σ: Store) = s match {

  // }

  // // refine scratchpad or store based on given expression, for branch statements
  // // return (storeTrue, storeFalse, scratchpadTrue, scratchpadFalse)
  // def branchRef(τ:Trace, e:Exp, σ:Store, ß:Scratchpad, ρ:Env): (Store,Store,Scratchpad,Scratchpad) = {
  //   import notjs.abstracted.interpreter.notJS.Mutable
  //   e match {
  //     // begin boolean refinement
  //     case x:PVar ⇒ {
  //       // foreach address a in rho(x), set a2v(a).b = True in true branch
  //       //                                             False in false branch
  //       if (!Mutable.refBool) {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         return (σ,σ,ß,ß)
  //       }
  //       if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}

  //       val as = ρ(x)
  //       if (as.size == 1) {
  //         val oldBV = σ(as)
  //         val (newBVT, newBVF) = (Bool.inject(Bool.True), Bool.inject(Bool.False)) 
  //         (σ + (as → newBVT), σ + (as → newBVF), ß, ß)  
  //       } else (σ, σ, ß, ß)        
  //     }
  
  //     case x:Scratch ⇒ {
  //       if (!Mutable.refBool) {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         return (σ,σ,ß,ß)
  //       }
  //       if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
        
  //       val oldBV = ß(x)
  //       val (newBVT, newBVF) = (Bool.inject(Bool.True), Bool.inject(Bool.False)) 
  //       (σ,σ,ß(x) = newBVT, ß(x) = newBVF)
  //     }

  //     case Binop(⌜⋆⌝, el, er) ⇒ {
  //       if (!Mutable.refBool) {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         return (σ,σ,ß,ß)
  //       }
  //       if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
  //       import notjs.abstracted.eval.Eval
  //       val objbv = Eval.eval(el, ρ, σ, ß )
  //       val strbv = Eval.eval(er, ρ, σ, ß )

  //       refineLookup(objbv, strbv.str, σ) match {
  //         case Some((addr, o)) ⇒ {
            
  //           val oldBV = o(strbv.str) match {
  //             case Some(bv) ⇒ bv
  //             case _ ⇒ println("err"); sys.error("refineLookup returned bad object")
  //           }
  //           val (newBVT, newBVF) = (Bool.inject(Bool.True), Bool.inject(Bool.False)) 
  //           // create the new objects
  //           val _oT = o copy (extern = o.extern ++ (strbv.str -> newBVT))          
  //           val _oF = o copy (extern = o.extern ++ (strbv.str -> newBVF))
  //           val _σT = σ.putObjStrong(addr, _oT)
  //           val _σF = σ.putObjStrong(addr, _oF)    
  //           (_σT,_σF,ß,ß) 
  //         }
  //         case _ ⇒ (σ,σ,ß,ß)
  //       }
  //     }     
  //     // end boolean refinement
  
  //     // begin isPrim refinement
  //     case Unop(IsPrim, ein) ⇒ {
  //       if (!Mutable.refIsPrim) {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         return (σ,σ,ß,ß)
  //       }

  //       ein match {
  //         case x:PVar ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
            

  //           val as = ρ(x)
  //           if (as.size == 1) {
  //             val oldBV = σ(as)
  //             val newBVT = oldBV copy (as = Addresses())
  //             val newBVF = oldBV.onlyAddr
  //             (σ + (as → newBVT), σ + (as → newBVF), ß, ß)  
  //           } else (σ,σ,ß,ß)    
  //         }
  
  //         case x:Scratch ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
            
  //           val oldBV = ß(x)
  //           val newBVT = oldBV copy (as = Addresses())
  //           val newBVF = oldBV.onlyAddr
  //           (σ, σ, ß(x) = newBVT, ß(x) = newBVF)
  //         }
  
  //         case Binop(⌜⋆⌝, el, er) ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
  //           import notjs.abstracted.eval.Eval
  //           val objbv = Eval.eval(el, ρ, σ, ß )
  //           val strbv = Eval.eval(er, ρ, σ, ß )

  //           refineLookup(objbv, strbv.str, σ) match {
  //             case Some((addr, o)) ⇒ {
                
  //               val oldBV = o(strbv.str) match {
  //                 case Some(bv) ⇒ bv
  //                 case _ ⇒ println("err"); sys.error("refineLookup returned bad object")
  //               }
  //               // create the new BVs
  //               val newBVT = oldBV copy (as = Addresses())
  //               val newBVF = oldBV.onlyAddr
  //               // create the new objects
  //               val _oT = o copy (extern = o.extern ++ (strbv.str -> newBVT))          
  //               val _oF = o copy (extern = o.extern ++ (strbv.str -> newBVF))
  //               val _σT = σ.putObjStrong(addr, _oT)
  //               val _σF = σ.putObjStrong(addr, _oF)    
  //               (_σT,_σF,ß,ß) 
  //             }
  //           case _ ⇒ (σ,σ,ß,ß)
  //         }
  //       }
  //       case _ ⇒ {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         (σ,σ,ß,ß)
  //       }
  //     }
  //   }
  //     // end isPrim refinement

  //     // begin ToBool refinement
  //     case Unop(ToBool, ein) ⇒ {
  //       if (!Mutable.refToBool) {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         return (σ,σ,ß,ß)
  //       }

  //       ein match {
  //         case x:PVar ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}      

  //           val as = ρ(x)
  //           if (as.size == 1) {
  //             val oldBV = σ(as)
  //             val newBVT = oldBV.removeNullAndUndef
  //             (σ + (as → newBVT), σ, ß, ß)  
  //           } else (σ,σ,ß,ß)    
  //         }
  
  //         case x:Scratch ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
            
  //           val oldBV = ß(x)
  //           val newBVT = oldBV.removeNullAndUndef
  //           (σ, σ, ß(x) = newBVT, ß)
  //         }
  
  //         case Binop(⌜⋆⌝, el, er) ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
  //           import notjs.abstracted.eval.Eval
  //           val objbv = Eval.eval(el, ρ, σ, ß )
  //           val strbv = Eval.eval(er, ρ, σ, ß )

  //           refineLookup(objbv, strbv.str, σ) match {
  //             case Some((addr, o)) ⇒ {
                
  //               val oldBV = o(strbv.str) match {
  //                 case Some(bv) ⇒ bv
  //                 case _ ⇒ println("err"); sys.error("refineLookup returned bad object")
  //               }
  //               // create the new BVs
  //               val newBVT = oldBV.removeNullAndUndef
  //               // create the new objects
  //               val _oT = o copy (extern = o.extern ++ (strbv.str -> newBVT))  
  //               val _σT = σ.putObjStrong(addr, _oT)
  //               (_σT,σ,ß,ß) 
  //             }
  //           case _ ⇒ (σ,σ,ß,ß)
  //         }
  //       }
  //       case _ ⇒ {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         (σ,σ,ß,ß)
  //       }
  //     }
  //   }
  //     // end ToBool refinement
  
  //     case b@Binop(opo, el, er) ⇒ {
  //       if (!Mutable.refTypeof) {
  //         if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //         return (σ,σ,ß,ß)
  //       }

  //       def canDoTypeofRefine(b: Binop): Option[(Exp, String)] = {
  //         b match {
  //           case Binop(⌜≡⌝, StrAST(s), Unop(Typeof, e)) ⇒ Some(e, s)
  //           case Binop(⌜≈⌝, StrAST(s), Unop(Typeof, e)) ⇒ Some(e, s)
  //           case Binop(⌜≡⌝, Unop(Typeof, e), StrAST(s)) ⇒ Some(e, s)
  //           case Binop(⌜≈⌝, Unop(Typeof, e), StrAST(s)) ⇒ Some(e, s)
  //           case _ ⇒ None
  //         }
  //       }

  //       canDoTypeofRefine(b) match {
  //         case Some((exp, str)) ⇒ {
  //           exp match {
  //             case x:PVar ⇒ {
  //               if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
  //               val as = ρ(x)
  //               if (as.size == 1) {
  //                 val oldBV = σ(as)
  //                 val (newBVT, newBVF) = refTypeof(σ(as), str, σ)  
  //                 (σ + (as → newBVT), σ + (as → newBVF), ß, ß)  
  //               } else (σ,σ,ß,ß)
  //             }
  
  //             case x:Scratch ⇒ {
  //               if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
  //               val (newBVT, newBVF) = refTypeof(ß(x), str, σ)
  //               (σ,σ,ß(x) = newBVT, ß(x) = newBVF)
  //             }
  
  //             case Binop(⌜⋆⌝, elll, errr) ⇒ {
  //               if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, true)}
  //               import notjs.abstracted.eval.Eval
  //               val objbv = Eval.eval(elll, ρ, σ, ß )
  //               val strbv = Eval.eval(errr, ρ, σ, ß )

  //               refineLookup(objbv, strbv.str, σ) match {
  //                 case Some((addr, o)) ⇒ {
                    
  //                   val oldBV = o(strbv.str) match {
  //                     case Some(bv) ⇒ bv
  //                     case _ ⇒ println("err"); sys.error("refineLookup returned bad object")
  //                   }
  //                   // create the new BV
  //                   val (newBVT, newBVF) = refTypeof(oldBV, str, σ) 
  //                   // create the new objects
  //                   val _oT = o copy (extern = o.extern ++ (strbv.str -> newBVT))          
  //                   val _oF = o copy (extern = o.extern ++ (strbv.str -> newBVF))
  //                   val _σT = σ.putObjStrong(addr, _oT)
  //                   val _σF = σ.putObjStrong(addr, _oF)    
  //                   (_σT,_σF,ß,ß) 
  //                 }
  //                 case None ⇒ (σ,σ,ß,ß)
  //               }
  //             } 
  //             case _ ⇒ {
  //               if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //               (σ,σ,ß,ß)
  //             }
  //           }
  //         } 
  //         case None ⇒ {
  //           if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //           (σ,σ,ß,ß)
  //         }
  //       }
  //     }
  //     case _ ⇒ {
  //       if (notJS.Mutable.stats) {Stats.nondetBranch(τ, e, false)}
  //       (σ,σ,ß,ß)
  //     }
  //   }
  // }

  // compare two expressions for equality
  // that is, left === right everywhere but ID

  def expEquals(left:Exp, right:Exp):Boolean = {
    (left.funcId == right.funcId) && (left match {
      // begin base cases: 1 level of unwrapping
      case NumAST(x) ⇒ {
        right match {
          case NumAST(y) ⇒ x == y
          case _ ⇒ false
        }
      }
      case BoolAST(x) ⇒ {
        right match {
          case BoolAST(y) ⇒ x == y
          case _ ⇒ false
        }
      }
      case StrAST(x) ⇒ {
        right match {
          case StrAST(y) ⇒ x == y
          case _ ⇒ false
        }
      }
      case UndefAST() ⇒ {
        right match {
          case UndefAST() ⇒ true
          case _ ⇒ false
        }
      }
      case NullAST() ⇒ {
        right match {
          case NullAST() ⇒ true
          case _ ⇒ false
        }
      }
      case PVar(x) ⇒ {
        right match {
          case PVar(y) ⇒ x == y
          case _ ⇒ false
        }
      }
      case sl:Scratch ⇒ {
        right match {
          case sr:Scratch ⇒ (sl.n == sr.n) && (sl.funcId == sr.funcId)
          case _ ⇒ false
        }
      }
      // end base cases

      // recursive cases
      case Binop(opl, e1l, e2l) ⇒ {
        right match {
          case Binop(opr, e1r, e2r) ⇒ ((opl == opr) && (expEquals(e1l, e1r)) && (expEquals(e2l, e2r)))
          case _ ⇒ false
        }
      }

      case Unop(opl, el) ⇒ {
        right match {
          case Unop(opr, er) ⇒ ((opl == opr) && (expEquals(el, er)) )
          case _ ⇒ false
        }
      }

    } )
  }

  // deviation from the semantics document: we don't generate
  // addresses here, instead we generate them using the trace and pass
  // them in here
  def alloc( σ:Store, as:List[Address], bvs:List[BValue] ): Store =
    σ alloc (as zip bvs)

  def alloc( σ:Store, a:Address, κs:KStack ): Store =
    σ alloc( a, κs )

  
  // deviation from the semantics document: we don't generate the
  // address here, instead we generate it using the trace and pass it
  // in here.
  def allocFun( clo:Closure, n:BValue, a:Address, σ:Store ): Store = {
    val intern = Map(
      proto → Address.inject(Function_prototype_Addr),
      classname → CFunction,
      code → Set(clo)
    )
    val extern = ExternMap() ++ (length → n)
    σ alloc (a, Object(extern, intern, Set(length)))
  }


  // deviation from the semantics document: we don't generate the
  // address here, instead we generate it using the trace and pass it
  // in here. it is possible for one allocation site to allocate more
  // than one class of object, but we need to guarantee that each
  // address maps to only one class of object. therefore we reserve a
  // range of |JSClass| possible addresses for each object allocation
  // site——the address passed in is the first element in that range,
  // and we modify it as needed for each class allocated here.
  def allocObj(bv:BValue, a:Address, σ:Store, τ:Trace): (Store, BValue) = {
    val class1 = bv.as.groupBy[JSClass]( classFromAddress(_) )
    val classes = 
      if ( bv.defAddr ) class1
      else class1 get CObject match {
        case Some(as) ⇒ class1 + (CObject → (as + Object_prototype_Addr))
        case None ⇒ class1 + (CObject → Set(Object_prototype_Addr))
      }

    val addrs:Map[JSClass, Address] = classes map {
      case (c, _) ⇒ (c, τ.modAddr(a, c))
    }

    val pas:Map[JSClass,BValue] = classes map {
      case (c, as) ⇒ c → Addresses.inject(as.foldLeft( Addresses() )(
        (acc, a) ⇒ (σ getObj a)(prototype) match {
          case Some(proto) ⇒
            if ( proto.defAddr ) acc ++ proto.as
            else acc ++ proto.as + Object_prototype_Addr

          case _ ⇒ acc + Object_prototype_Addr
        }))
    }

    val intern:Map[JSClass,Map[Str,Any]] = classes map {
      case (c, _) ⇒ c → Map(proto → pas(c), classname → c)
    }

    val σ1 = classes.keys.foldLeft( σ )( (acc, c) ⇒ {
      val o = Object(ExternMap(), intern(c), Set())
      acc alloc( addrs(c), o )
    })

    val bv1 = Addresses.inject( addrs.values.toSet )
    
    (σ1, bv1)
  }



  def applyClo( bv1:BValue, bv2:BValue, bv3:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad, κs:KStack, τ:Trace ): Set[State] = {
    // until we do value refinement, we are going to cast bv2 to addresses
    // TODO: change bv2as back to bv2 after value refinement
    val bv2as = Addresses.inject(bv2.as)
    // the translator should guarantee that bv2 and bv3 do contain
    // addresses and only addresses, and the args address is a singleton
    assert( bv2as.defAddr && bv3.defAddr && bv3.as.size == 1 )

    val isctor = (σ getObj bv3.as.head) calledAsCtor

    // for store pruning (if enabled): get the set of object roots,
    // which will be the same for all callees. note that we don't
    // include ß, since that is unreachable by the callee.
    //
    // !! OPT: we could go ahead and prune the store based on oas here
    // and then prune the reachable result for vas for each
    // closure, rather than pruning for both oas and vas every
    // time from scratch.
    //
    val oas =
      if ( notJS.Mutable.pruneStore ) bv2.as ++ bv3.as ++ keepInStore
      else Addresses()

    // memoize the pruned store info based on the set of free
    // variables (specifically their addresses); if we have multiple
    // callees with the same set of free variables then we don't need
    // to prune separately for each one
    val memo = HashMap[Addresses, Store]()

    val (ςs, nonfun) = bv1.as.foldLeft( (Set[State](), false) )(
      (acc, a) ⇒ {
       (σ getObj a).getCode match {
       case clos if clos.nonEmpty ⇒ (acc._1 ++ (clos flatMap {
       case Clo(ρc, m @ Method(self, args, s)) ⇒
              // are we doing store pruning?
              if ( notJS.Mutable.pruneStore ) { // yes, prune store
                val vas = ρc.addrs
                val reach_σ = memo get vas match { // check the cache
                    case None ⇒ // prune to get reachable/unreachable stores
                      val (rσ, uσ) = σ.prune( vas, oas )
                      PruneStoreToo(τ) = (uσ, ß)
                      memo(vas) = rσ
                      rσ

                    case Some(stored) ⇒ // retrieve from memo
                      stored
                  }
                val τ1 = τ.update(ρc, σ, bv2as, bv3, s)

                /*StatsDeux.signature(m, τ1, bv3, σ) // !! STATS*/
                val ka = τ1.toAddr
                val as = List(τ1.makeAddr(self), τ1.makeAddr(args))
                val rσ1 = alloc( reach_σ, as, List(bv2as, bv3) )
                val rσ2 = alloc( rσ1, ka, κs push RetK(x, ρ, isctor, τ))
                val ρc1 = ρc ++ (List(self, args) zip as)
                // if there was an exception handler in the current function
                // update it to say that exception handler is some where up 
                // in the call stack
                val exc = if (κs.exc.head != 0) 1 else 0
                Set(
                  State(s, ρc1, rσ2, Scratchpad(0), KStack(AddrK(ka,m),exc), τ1)
                )
              }
              else { // no, only prune scratchpad
               val τ1 = τ.update(ρc, σ, bv2as, bv3, s)
               val ka = τ1.toAddr
               val as = List(τ1.makeAddr(self), τ1.makeAddr(args))
               val σ1 = alloc( σ, as, List(bv2as, bv3) )
               val σ2 = alloc( σ1, ka, κs push RetK(x, ρ, isctor, τ))
               val ρc1 = ρc ++ (List(self, args) zip as)
                val exc = if (κs.exc.head != 0) 1 else 0
                PruneScratch(τ) = ß
                Set(
                  State(s, ρc1, σ2, Scratchpad(0), KStack(AddrK(ka,m),exc), τ1)
                )
              }

            case Native(f) ⇒
              f( bv2as, bv3, x, ρ, σ, ß, κs, τ )
          }), acc._2)

       case _ ⇒ (acc._1, true)
        }
      })

    // if we're pruning then we need to worry about the following
    // problem: if this is the first time we're processing a callee
    // we're guaranteed that we'll eventually get to the corresponding
    // RetK (because the AddrK given to the callee will have never
    // been seen before). however, if it isn't the first time for any
    // of the callees then they could all converge, thus never getting
    // to the corresponding RetK. if that happens _and_ there is new
    // information in the unreachable store/ß then the analysis will
    // prematurely converge. to prevent this, we will compute the
    // trace for the immediately following Merge (guaranteed to be
    // there by the translator) and remember it in
    // notJS.Mutable.prunedInfo along with the current trace. after
    // the analysis converges, we will iterate through all of the
    // saved pruned information in PruneStoreToo and join it into the
    // appropriate memoized Merge states (determined by the merge
    // traces saved here) and if any of them change we'll add them
    // back to the worklist.
    //
    // IMPORTANT NOTE: this strategy only works if we're using a
    // stack-based trace, guaranteeing that the merge_τ we compute
    // below is the same one that will be computed by the callee's
    // corresponding RetK. if we're using a non-stack-based trace then
    // the trace returned from a call can be completely different, and
    // this solution breaks.
    //
    // the second clause of the guard below that checks whether τ is
    // in PruneStoreToo is needed because the callees could all have
    // been Native closures, in which case we never pruned anything.
    //
    if ( notJS.Mutable.pruneStore && (PruneStoreToo contains τ) ) {
      val merge_τ = κs.top match {
        case SeqK((s:Merge) :: tl) ⇒ τ update s
        case _ ⇒ sys.error("translator reneged")
      }
      val as = x match {
        case pv:PVar ⇒ ρ(pv)
        case _ ⇒ Addresses()
      }
      notJS.Mutable.prunedInfo(merge_τ) = (τ, x, as)
    }

    // check callee states for error states
     if (ςs.exists(s ⇒ s.t match {
      case ValueT(ev:EValue) ⇒ true
      case _ ⇒ false
      }) ) StatsDeux.except(x.id, typeError) // !! STATS

    // return the callee states plus potentially a typeError state
    ςs ++ (
      if (nonfun ){
          /*
          if (notJS.Mutable.stats) {
            Stats.raisedExc(e)
          } */
          StatsDeux.except(x.id, typeError ) // !! STATS
          Set(State(typeError, ρ, σ, ß, κs, τ))
        } 
      else Set()
    )
  }

  def delete(bv1:BValue, bv2:BValue, x:Scratch, ρ:Env, σ:Store, ß:Scratchpad): (Option[(Store, Scratchpad)], Option[EValue]) = {
    val isStrong = bv1.as.size == 1 && σ.isStrong(bv1.as.head)

    val (defPresent, defAbsent) = bv1.as.foldLeft( (true, true) )(
      (acc, a) ⇒ {
        val o = σ getObj a
        val dp = 
          if ( acc._1 )
            o.defField(bv2.str) && 
            !(nodelete(o.getJSClass) contains bv2.str)
          else false
        val da = 
          if ( acc._2 && !dp ) 
            o.defNotField(bv2.str) ||
            (nodelete(o.getJSClass) contains bv2.str)
          else false

        (dp, da)
      })

    val noexc =
      if ( bv1.as.isEmpty )
        None
      else if ( defAbsent ) {
        Some((σ, ß(x) = Bool.FalseBV))
      }
      else if ( defPresent ) {
        if ( isStrong ) {
          val a = bv1.as.head
          val σ1 = σ putObjStrong(a, (σ getObj a) −− bv2.str)
          Some((σ1, ß(x) = Bool.TrueBV))
        }
        else {
          val σ1 = bv1.as.foldLeft( σ )(
            (acc, a) ⇒ acc putObjWeak(a, (acc getObj a) − bv2.str) )
          Some((σ1, ß(x) = Bool.TrueBV))
        }
      }
      else {
        val σ1 = bv1.as.foldLeft( σ )(
          (acc, a) ⇒ acc putObjWeak(a, (acc getObj a) − bv2.str) )
        Some((σ1, ß(x) = Bool.TopBV))
      }

    val exc =
      if ( bv1.nil == Null.⊤ || bv1.undef == Undef.⊤ )
        Some(typeError)
      else
        None

    (noexc, exc)
  }


  // NOTE: getProto and getJSClass are implemented in the Object class
  // NOTE: initState is contained in init.scala
  // NOTE: inject is implemented either in the subdomain's companion
  //       object or, for addresses, in BValue's companion object


  def lookup( as:Addresses, str:Str, σ:Store ): BValue = {
    def look( o:Object ): BValue = {
      val local = o(str).toSet
      val chain = 
      	if ( !o.defField(str) )
      	  o.getProto.as.map( (a) ⇒ look(σ getObj a) )
      	else
      	  Set()
      val fin =
      	if ( !o.defField(str) && o.getProto.nil == Null.⊤ )
      	  Set(Undef.BV)
      	else
      	  Set()

      (local ++ chain ++ fin).reduceLeft( (acc, bv) ⇒ acc ⊔ bv )
    }

    as.foldLeft( BValue.⊥ )( (acc, a) ⇒ acc ⊔ look(σ getObj a) )
  }


  // NOTE: there is no nextK; that functionality is implemented
  //       directly in the transition rules in interpreter.scala


  // retrieve all keys accessible via this object, including ones in
  // the prototype chain. we optimize the keyset by removing keys that
  // are over-approximated by other keys in the set
  def objAllKeys( bv:BValue, σ:Store ): Set[Str] = {
    def recur( a:Address ): Set[Str] = {
      val o = σ getObj a
      o.getProto.as.foldLeft( o.fields )(
        (acc, a) ⇒ acc ++ recur(a) )
    }

    val keys = bv.as.flatMap( recur(_) )
    Str.minimize( keys )
  }


  // note that we add the constructor with a strong update to the
  // object and address without checking whether the address is weak;
  // this is OK because the translator guarantees that all concrete
  // addresses represented by the abstract address would also be
  // marked as constructors.
  def setConstr( σ:Store, bv:BValue ): Store = {
    assert( bv.as.size == 1 )
    val o = σ getObj bv.as.head
    val o1 = Object( o.extern, o.intern + (constructor → true), o.present )
    σ putObjStrong( bv.as.head, o1 )
  }

  
  // NOTE: there is no specialK; that functionality is implemented
  //       directly in the transition rules in interpreter.scala


  // factored out of toObj to avoid duplication in Object constructor
  // this implements most of toObj's functionality
  def toObjBody(bv: BValue, σ: Store, τ: Trace, a: Address): (BValue, Store, Set[Domain]) = {
    // TODO: fix nonexhaustive match warning?
    val sorts = bv.sorts & Set( DAddr, DNum, DBool, DStr )

    val (bv1, σ1) = sorts.foldLeft( (BValue.⊥, σ) )(
      (acc, sort) ⇒ sort match {
        case DAddr ⇒
          (acc._1 ⊔ Addresses.inject(bv.as), acc._2)

        case DNum ⇒
          val (σ2, bv2) = allocObj(Address.inject(Number_Addr), a, acc._2, τ)
          assert( bv2.as.size == 1 )
          val o = σ2 getObj bv2.as.head
          val o1 = Object(o.extern, o.intern + (value → bv.onlyNum), o.present)
          (acc._1 ⊔ bv2, σ2 putObj( bv2.as.head, o1 ))

        case DBool ⇒
          val (σ2, bv2) = allocObj(Address.inject(Boolean_Addr), a, acc._2, τ)
          assert( bv2.as.size == 1 )
          val o = σ2 getObj bv2.as.head
          val o1 = Object(o.extern, o.intern + (value → bv.onlyBool), o.present)
          (acc._1 ⊔ bv2, σ2 putObj( bv2.as.head, o1 ))

        case DStr ⇒
          val (σ2, bv2) = allocObj(Address.inject(String_Addr), a, acc._2, τ)
          assert( bv2.as.size == 1 )
          val o = σ2 getObj bv2.as.head
          // set the external fields length and indices 0 to length-1
          val exactStr = Str.getExact(bv.str)
          val extern = exactStr match {
            case Some(s) ⇒ 
              List.range(0, s.length).foldLeft(
                o.extern ++ (length → Num.inject(NConst(s.length))))(
                  (acc, e) ⇒ acc ++ 
                    (Str.α(e.toString) → Str.inject(Str.α(s(e).toString))))

            case None ⇒ 
              (o.extern + (length → Num.inject(NReal))) + 
                (SNum → Str.inject(STop))
          }
          val intern1 = o.intern + (value → bv.onlyStr)
          val o1 = Object(extern, intern1, o.present + length)
          (acc._1 ⊔ bv2, σ2 putObj( bv2.as.head, o1 ))

        case _ ⇒
          sys.error("suppresses compiler warning; this case can't happen")
      })

    (bv1, σ1, sorts)
  }

  def toObj( bv:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad, τ:Trace ): (Option[(BValue, Store, Scratchpad)], Option[EValue]) = {
    val (bv1, σ1, sorts) = toObjBody(bv, σ, τ, τ makeAddr x)

    val noexc =
      if ( sorts.nonEmpty ) x match {
        case pv:PVar ⇒
          Some((bv1, σ1 + (ρ(pv) → bv1), ß))

        case sc:Scratch ⇒
          Some((bv1, σ1, ß(sc) = bv1))
      }
      else None

    val exc = 
      if ( bv.nil == Null.⊤ || bv.undef == Undef.⊤ ) Some(typeError)
      else None

    (noexc, exc)
  }


  // NOTE: there is no update; that functionaliy is implemented
  //       directly in the store


  // this isn't quite the same as the semantics for efficiency
  // reasons: rather than creating a bunch of objects using strong
  // updates and then joining them together to account for weak
  // updates, we figure out which one we're doing from the start.
  def updateObj(bv1:BValue, bv2:BValue, bv3:BValue, σ:Store): (Option[(BValue, Store)], Option[EValue]) = {
    val str = bv2.str
    val maybeLength = length ⊑ str
    val isStrong = bv1.as.size == 1 && σ.isStrong(bv1.as.head)
    val bv3num = bv3.tonum
    lazy val maybeArray = bv1.as exists (a ⇒ (σ getObj a).getJSClass == CArray)
    lazy val rhsMaybeU32 = Num.maybeU32( bv3num )
    lazy val propertyMaybeU32 = Num.maybeU32( Num.inject(str.toNum) )

    val noexc =
      if ( isStrong ) {
        val o = σ getObj bv1.as.head
        val o1 =
          if ( !maybeArray ) o ++ (str → bv3)
          else if ( !maybeLength ) 
            o ++ (str → bv3) ++ (length → Num.inject(Num.U32))
          else if ( str != length ) 
            (o − Str.u32) ++ (str → bv3) ++ (length → Num.inject(Num.U32))
          else 
            // !!TODO: we can be more precise in this else case
            (o − Str.u32) ++ (str → Num.inject(Num.U32)) 
        val σ1 = σ putObjStrong( bv1.as.head, o1 )
        Some((bv3, σ1))
      }
      else if ( bv1.as.nonEmpty ) {
       	val σ1 = bv1.as.foldLeft( σ )(
          (acc, a) ⇒ {
            val o = acc getObj a

            if ( o.getJSClass == CArray ) {
              val o1 = 
                if ( maybeLength && rhsMaybeU32 )
                  (o − Str.u32) + (str → bv3)
                else 
                  o + (str → bv3)
              val o2 =     
                if ( propertyMaybeU32 )
                  o1 + (length → Num.inject(Num.U32))
                else 
                  o1 
              acc putObjWeak(a, o2)
            }
            else 
              acc putObjWeak(a, o + (str → bv3))
        })
        Some((bv3, σ1))
      }
      else
        None

    val exc =
      if ( bv1.nil == Null.⊤ || bv1.undef == Undef.⊤ )
        Some(typeError)
      else if ( maybeArray && maybeLength && Num.maybenotU32( bv3 ) )
        Some(rangeError)
      else
        None

    (noexc, exc)
  }
}
