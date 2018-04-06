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
      case Binary(bop, e1, e2) => ren(env,e1) flatMap{ e1p =>
        ren(env,e2) map {e2p =>
          Binary(bop,e1p,e2p)
        }
      }
      case If(e1, e2, e3) => ren(env,e1) flatMap{ e1p =>
        ren(env,e2) flatMap{ e2p =>
        ren(env,e2) map { e3p =>
          If(e1p,e2p,e3p)
        }
      }
      }

      case Var(x) => doreturn(Var(lookup(env,x)))

      case Decl(m, x, e1, e2) => fresh(x) flatMap { xp =>
        ren(extend(env,x,xp),e2) flatMap {
          e2p => ren(extend(env,x,x),e1) map {
            e1p => Decl(m,xp,e1p,e2p)
          }
        }
      }

      case Function(p, params, retty, e1) => {
        val w: DoWith[W,(Option[String], Map[String,String])] = p match {
          case None => doreturn(None,env)
          case Some(x) => fresh(x) map {xp => (Some(xp),extend(env,x,xp))}
        }
        w flatMap { case (pp, envp) =>
          params.foldRight[DoWith[W,(List[(String,MTyp)],Map[String,String])]]( doreturn((Nil, envp)) ) {
            case ((x,mty), acc) => acc flatMap {
              case (accL, accM) => fresh(x) map { xp => ((xp -> mty)::accL, extend(accM,x,xp))}
            }
          } flatMap {
            case (paramsp,envpp) => ren(envpp,e1) map { e1p => Function(pp,paramsp,retty,e1p)}
          }
        }
      }

      case Call(e1, args) => args.foldRight[DoWith[W,List[Expr]]](doreturn(Nil)) {
        (arg,acc) =>
          acc flatMap {
            accp => ren(env,arg) map {al => al::accp}
          }
      } flatMap {
        argsp => ren(env,e1) map {e1p => Call(e1p,argsp)}
      }

      case Obj(fields) => fields.foldRight[DoWith[W,Map[String,Expr]]](doreturn(Map.empty)){
        (f, acc) =>
          acc flatMap{
            accp => ren(env,f._2) map {ep => extend(accp, f._1,ep)}
          }
      } map {fp => Obj(fp)}
      case GetField(e1, f) => ren(env,e1) map {e1p => GetField(e1p,f)}

      case Assign(e1, e2) => ren(env,e1) flatMap { e1p => ren(env,e2) map {e2p => Assign(e1p,e2p)}}

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
    ren(env, e)
  }

  def myuniquify(e: Expr): Expr = {
    val fresh: String => DoWith[Int,String] = { _ =>
      doget flatMap{ counter => doput(counter+1) map { _ => "x"+counter.toString}}
    }
    val (_, r) = rename(empty, e)(fresh)(0)
    r
  }

  /*** Helper: mapFirst to DoWith ***/

  // List map with an operator returning a DoWith
  def mapWith[W,A,B](l: List[A])(f: A => DoWith[W,B]): DoWith[W,List[B]] = {
    l.foldRight[DoWith[W,List[B]]]( doreturn(List()) ) {
      (a,acc) => f(a) flatMap{
        b => acc map{
          l => b::l
        }
      }
    }
  }

  // Map map with an operator returning a DoWith
  def mapWith[W,A,B,C,D](m: Map[A,B])(f: ((A,B)) => DoWith[W,(C,D)]): DoWith[W,Map[C,D]] = {
    m.foldRight[DoWith[W,Map[C,D]]]( doreturn(Map()) ) {
      (a,acc) => f(a) flatMap{
        c => acc map{
          m => m+c
        }
      }
    }
  }

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](l: List[A])(f: A => Option[DoWith[W,A]]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(l)
    case h :: t =>  f(h) match{
      case Some(x) => x.map((x:A) => x::t)
      case None => mapFirstWith(t)(f).map((x:List[A]) => h::x)
    }
  }

  // There are better ways to deal with the combination of data structures like List, Map, and
  // DoWith, but we won't tackle that in this assignment.

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
      /***** Make sure to replace the case _ => ???. */
    case (TNull, TObj(_)) => true
    case (_,_) if t1 == t2 => true
    case (TObj(f1), TObj(f2)) => f1.forall{
      case (f,t) => f2.get(f) match {
        case None => true
        case Some(tp) => if(t == tp) true else false
      }
    }
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
    case TObj(fields) if (fields exists { case (_, typ) => hasFunctionTyp(typ) }) => true
    case _ => false
  }

  def isBindex(m: Mode, e: Expr): Boolean = m match {
    case MRef => isLExpr(e)
    case MConst => true
    case MName => true
    case MVar => true
    case _ => throw new UnsupportedOperationException
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => lookup(env,x).t
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typeof(env,e1) match {
        case TBool => TBool
        case tgot => err(tgot,e1)
      }
      case Binary(Plus, e1, e2) => typeof(env,e1) match {
        case TNumber => if (typeof(env,e2) == TNumber) TNumber else err(typeof(env,e2),e2)
        case TString => if (typeof(env,e2) == TString) TString else err(typeof(env,e2),e2)
        case tgot => err(tgot,e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => typeof(env,e1) match {
        case TNumber => if(typeof(env,e2) == TNumber) TNumber else err(typeof(env,e2),e2)
        case tgot => err(tgot,e1)
      }
      case Binary(Eq|Ne, e1, e2) => if (hasFunctionTyp(typeof(env,e1))) err(typeof(env,e1),e1)
      else if (hasFunctionTyp(typeof(env,e2))) err(typeof(env,e2),e2)
      else if (typeof(env,e1) == typeof(env,e2)) TBool else err(typeof(env,e2),e2)
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typeof(env,e1) match {
        case TNumber => if (typeof(env,e2) == TNumber) TBool else err(typeof(env,e2),e2)
        case TString => if(typeof(env,e2) == TString) TString else err(typeof(env,e2),e2)
        case tgot => err(tgot,e1)
      }
      case Binary(And|Or, e1, e2) => typeof(env,e1) match {
        case TBool => if (typeof(env,e2) == TBool) TBool else err(typeof(env,e2),e2)
        case tgot => err(tgot,e1)
      }

      case Binary(Seq, e1, e2) =>
        typeof(env,e1)
        typeof(env,e2)

      case If(e1, e2, e3) => typeof(env,e1) match {
        case TBool => if(typeof(env,e2) == typeof(env,e3)) typeof(env,e2) else err(typeof(env,e3),e3)
        case tgot => err(tgot,e1)
      }

      case Obj(fields) => TObj(fields.map( { case (s,ei) => (s, typeof(env,ei))}))

      case GetField(e1, f) => typeof(env,e1) match {
        case TObj(fields) => fields.get(f) match {
          case Some(x) => x
          case None => err(typeof(env,e1),e1)
        }
        case tgot => err(tgot,e1)
      }

        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(m, x, e1, e2) => if (isBindex(m,e1)) typeof(extend(env,x,MTyp(m,typeof(env,e1))),e2)
        else err(typeof(env,e1),e1)

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            extend(env,f, MTyp(MConst,tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1) { case (acc, (xi,mi)) => extend(acc, xi, MTyp(mi.m, mi.t))}
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params,typeof(env2,e1))
          case Some(tret) => if (TFunction(params,typeof(env2,e1)) == TFunction(params,tret)) TFunction(params,tret)
            else err(typeof(env2,e1),e1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params, args).zipped.foreach {
            case ((_, m), ei) =>
              if(m.t == typeof(env,ei) || isBindex(m.m, e1)) typeof(env,ei) else err(typeof(env,ei),ei)
          }
          tret
        case tgot => err(tgot, e1)
      }

        /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) => lookup(env,x) match {
        case MTyp(MVar,t) if (typeof(env,e1) == t) => t
        case MTyp(MRef,t) if (typeof(env,e1) == t) => t
        case _ => err(typeof(env,e1),e1)
      }
      case Assign(GetField(e1, f), e2) => typeof(env,e1) match {
        case TObj(field) => field.get(f) match {
          case Some(x) if (typeof(env,e2) == x) => x
          case _ => err(typeof(env,e2),e2)
        }
      }
      case Assign(_, _) => err(TUndefined, e)

      case Null => TNull

      case Unary(Cast(t), e1) => typeof(env, e1) match {
        case tgot if castOk(tgot,t) => tgot
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
      rename[Unit](e)(???){ x => ??? }
    }

    subst(???)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = ???

  def getBinding(mode: Mode, e: Expr): DoWith[Mem,Expr] = {
    require(!isRedex(mode,e), s"expression ${e} must not reducible under mode ${mode}")
    ???
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, v1) if isValue(v1) => ???
        /***** More cases here */
        /***** Cases needing adapting from Lab 4. */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        ???
      case GetField(a @ A(_), f) =>
        ???

      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        ???
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        ???

        /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) =>
        ???

      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m => ??? } map { _ => ??? }

      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        ???

      case Call(v @ Function(p, params, _, e), args) => {
        val pazip = params zip args
        if (???) {
          val dwep = pazip.foldRight( ??? : DoWith[Mem,Expr] )  {
            case (((xi, MTyp(mi, _)), ei), dwacc) => ???
          }
          p match {
            case None => ???
            case Some(x) => ???
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

      case Decl(mode, x, e1, e2) =>
        ???
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
