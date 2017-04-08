package jsy.student

import jsy.lab5.Lab5Like

object Lab5 extends jsy.util.JsyApplication with Lab5Like {
  import jsy.lab5.ast._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * <Your Name>
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*** Exercise with DoWith ***/

  def rename[W](env: Map[String,String], e: Expr)(fresh: String => DoWith[W,String]): DoWith[W,Expr] = {
    def ren(env: Map[String,String], e: Expr): DoWith[W,Expr] = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => doreturn(e)
      case Print(e1) => ren(env,e1) map { e1p => Print(e1p) }

      case Unary(uop, e1) => ren(env,e1) map {e1p => Unary(uop,e1p)}
      case Binary(bop, e1, e2) => ren(env,e1) flatMap{e1p=>
        ren(env,e2) map (e2p => Binary(bop,e1p,e2p))}
      case If(e1, e2, e3) => ???

      case Var(x) => ???

      case Decl(m, x, e1, e2) => fresh(x) flatMap { xp =>
        ???
      }

      case Function(p, params, retty, e1) => {
        val w: DoWith[W,(Option[String], Map[String,String])] = p match {
          case None => ???
          case Some(x) => ???
        }
        w flatMap { case (pp, envp) =>
          params.foldRight[DoWith[W,(List[(String,MTyp)],Map[String,String])]]( doreturn((Nil, envp)) ) {
            case ((x,mty), acc) => acc flatMap {
              ???
            }
          } flatMap {
            ???
          }
        }
      }

      case Call(e1, args) => ???

      case Obj(fields) => ???
      case GetField(e1, f) => ???

      case Assign(e1, e2) => ???

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
    ren(env, e)
  }

  def myuniquify(e: Expr): Expr = {
    val fresh: String => DoWith[Int,String] = { _ =>
      ???
    }
    val (_, r) = rename(empty, e)(fresh)(???)
    r
  }

  /*** Helper: mapFirst to DoWith ***/

  // List map with an operator returning a DoWith
  def mapWith[W,A,B](l: List[A])(f: A => DoWith[W,B]): DoWith[W,List[B]] = {
    l.foldRight[DoWith[W,List[B]]]( doreturn(Nil) ) { (a,dw)=>
      f(a).flatMap(r=>dw.map(r::_))
    }
  }

  // Map map with an operator returning a DoWith
  def mapWith[W,A,B,C,D](m: Map[A,B])(f: ((A,B)) => DoWith[W,(C,D)]): DoWith[W,Map[C,D]] = {
    m.foldRight[DoWith[W,Map[C,D]]]( doreturn(Map.empty)) {(a,dw)=>
      f(a).flatMap(r=>dw.map(_+r))
    }
  }

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](l: List[A])(f: A => Option[DoWith[W,A]]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(Nil)
    case h :: t => f(h) match{
      case None => mapFirstWith(t)(f).map(h::_)
      case Some(thing)=>thing.map((h)=>h::t)
    }
  }

  // There are better ways to deal with the combination of data structures like List, Map, and
  // DoWith, but we won't tackle that in this assignment.

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
      /***** Make sure to replace the case _ => ???. */
    case (t1,t2) if (t1==t2) => true
    case (TNull,TObj(_)) => true
    case (TObj(fields1), TObj(fields2)) =>
      val acc1 = fields2 forall {case (fieldName,ti) =>
        fields1.get(fieldName) match{
          case Some(t2) => if(ti == t2) true else false
          case None => false
        }}
      val acc2 = fields1 forall {case (fieldName,ti) =>
        fields2.get(fieldName) match{
          case Some(t2) => if(ti == t2) true else false
          case None => acc1
        }}
      acc1 || acc2
      /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ???
    case (_, TInterface(tvar, t2p)) => ???
      /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def isBindex(m: Mode, e: Expr): Boolean = m match {
    case MRef => isLExpr(e)
    case _ => true
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => ???
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1);
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Minus | Times | Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Eq | Ne, e1, e2) =>
        (typeof(env, e1), typeof(env, e2)) match {
          case (tgot, _) if (hasFunctionTyp(tgot)) => err(tgot, e1);
          case (_, tgot) if (hasFunctionTyp(tgot)) => err(tgot, e2);
          case (t1, t2) => if (t1 == t2) TBool else err(t2, e2)
        }
      case Binary(Lt | Le | Gt | Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1);
      }
      case Binary(And | Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (TBool, tgot) => err(tgot, e2);
        case (tgot, _) => err(tgot, e1);

      }
      case Binary(Seq, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (t1, t2) => t2
        case (tgot, _) => err(tgot, e1);
        case (_, tgot) => err(tgot, e2);
      }
      case If(e1, e2, e3) => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
        case (TBool, t2, t3) => if (t2 == t3) t2 else err(t2, e2)
        case (tgot, _, _) => err(tgot, e1);
        case (_, tgot, _) => err(tgot, e2);
        case (_, _, tgot) => err(tgot, e3);
      }

      case Obj(fields) => TObj(fields.mapValues { case (e1) => typeof(env, e1) })
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) => if (fields.contains(f)) fields(f) else err(typeof(env, e1), e1)
        case _ => err(typeof(env, e1), e1)

      }

        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(m, x, e1, e2) => ???
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            ???
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = ???
        // Match on whether the return type is specified.
        tann match {
          case None => ???
          case Some(tret) => ???
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params, args).zipped.foreach {
            ???
          }
          tret
        case tgot => err(tgot, e1)
      }

        /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) =>
        ???
      case Assign(GetField(e1, f), e2) =>
        ???
      case Assign(_, _) => err(TUndefined, e)

      case Null =>
        ???

      case Unary(Cast(t), e1) => typeof(env, e1) match {
        case tgot if ??? => ???
        case tgot => err(tgot, e1)
      }

      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case _ => ???
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => ???
      case Binary(bop, e1, e2) => ???
      case If(e1, e2, e3) => ???
      case Var(y) => ???
        /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
        /***** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) =>
        ???
        /***** Cases directly from Lab 4 */
      case Call(e1, args) => ???
      case Obj(fields) => ???
      case GetField(e1, f) => ???
        /***** New case for Lab 5 */
      case Assign(e1, e2) => ???

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }

    def myrename(e: Expr): Expr = {
      val fvs = freeVars(esub)
      def fresh(x: String): String = if (fvs contains x) fresh(x + "$") else x
      rename[Unit](e)(fvs){ x => doreturn(fresh(x)) }
    }

    subst(myrename(e))
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match{
    case MConst| MVar => (!isValue(e))
    case MRef => !isValue(e)
    case MName => false
  }

  def getBinding(mode: Mode, e: Expr): DoWith[Mem,Expr] = {
    require(!isRedex(mode,e), s"expression ${e} must not reducible under mode ${mode}")
    mode match{
      case MConst | MName | MRef => doreturn(e)
      case MVar => memalloc(e) map{address => Unary(Deref,address)}
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(x))  => doreturn((N(-x)))
        /***** More cases here */
        /***** Cases needing adapting from Lab 4. */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        memalloc(e)
      case GetField(a @ A(_), f) => doget map { w =>
        w.get(a) match {
          case Some(Obj(fields))=> fields(f)
        }

      }

      case Decl(MConst, x, v1, e2) if isValue(v1)  => doreturn(substitute(e2,v1,x))


      case Decl(MVar, x, v1, e2) if isValue(v1) => memalloc(v1).map(a => substitute(e2,Unary(Deref,a),x))


      /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) => doget map {state => state.get(a) match{
        case None => throw StuckError(e)
        case Some(ep) => ep
      }}

      case Unary(Cast(t),v)  if isValue(v)=> v match{
        case a @ A(_)=> doget map { w =>
          w.get(a) match {
            case Some(Obj(fields)) => t match{
              case TObj(tfields) => {
            if (tfields.forall {
            case (fi, ei) => tfields.get (fi) match {
            case Some (_) => true
            case None => false
            }
            }) a
            else throw StuckError (e)
            }
        }
          case None => throw StuckError(e)
          }
      }
        case _ => doreturn(v)
        }
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m =>  m + (a->v)} map { _ => v }

      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        domodify[Mem]{ m=> m.get(a) match {
          case Some(Obj(fields)) => m + (a -> Obj(fields + (f->v)))
        }} map {_ => v}

      case Call(v @ Function(p, params, _, e), args) => {
        val pazip = params zip args
        if (pazip forall { case(((_, MTyp(m,_)),e1)) => !isRedex(m, e1) }) {
          val dwep = pazip.foldRight(doreturn(e) : DoWith[Mem,Expr] )  {
            case (((xi, MTyp(mi, _)), ei), dwacc) => dwacc flatMap{acc=> getBinding(mi,ei) map{ep=>substitute(acc,ep,xi)}}
          }
          p match {
            case None => dwep
            case Some(x) => dwep map {ebody => substitute(ebody,v,x)}
          }
        }
        else {
          val dwpazipp = mapFirstWith(pazip) {
            ???
          }
          ???
        }
      }

      /* Base Cases: Error Rules */
        /***** Replace the following case with a case to throw NullDeferenceError.  */
      //case _ => throw NullDeferenceError(e)

      /* Inductive Cases: Search Rules */
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) =>
        ???
        /***** Cases needing adapting from Lab 4 */
      case GetField(e1, f) =>
        ???
      case Obj(fields) =>
        ???

      case Decl(mode, x, e1, e2) => ???

      case Call(e1, args) =>
        ???

        /***** New cases for Lab 5.  */
      case Assign(e1, e2) if ??? =>
        ???
      case Assign(e1, e2) =>
        ???

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def lower(e: Expr): Expr =
    /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
