package edu.uta.spl

abstract class TypeChecker {
  var trace_typecheck = false

  /** symbol table to store SPL declarations */
  var st = new SymbolTable

  def expandType ( tp: Type ): Type
  def typecheck ( e: Expr ): Type
  def typecheck ( e: Lvalue ): Type
  def typecheck ( e: Stmt, expected_type: Type )
  def typecheck ( e: Definition )
  def typecheck ( e: Program )
}


class TypeCheck extends TypeChecker {

  /** typechecking error */
  def error ( msg: String ): Type = {
    System.err.println("*** Typechecking Error: "+msg)
    System.err.println("*** Symbol Table: "+st)
    System.exit(1)
    null
  }

  /** if tp is a named type, expand it */
  def expandType ( tp: Type ): Type =
    tp match {
      case NamedType(nm)
        => st.lookup(nm) match {
          case Some(TypeDeclaration(t))
              => expandType(t)
          case _ => error("Undeclared type: "+tp)
        }
      case _ => tp
  }

  /** returns true if the types tp1 and tp2 are equal under structural equivalence */
  def typeEquivalence ( tp1: Type, tp2: Type ): Boolean =
    if (tp1 == tp2 || tp1.isInstanceOf[AnyType] || tp2.isInstanceOf[AnyType])
      true
    else expandType(tp1) match {
      case ArrayType(t1)
        => expandType(tp2) match {
              case ArrayType(t2)
                => typeEquivalence(t1,t2)
              case _ => false
           }
      case RecordType(fs1)
        => expandType(tp2) match {
              case RecordType(fs2)
                => fs1.length == fs2.length &&
                   (fs1 zip fs2).map{ case (Bind(v1,t1),Bind(v2,t2))
                                        => v1==v2 && typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case TupleType(ts1)
        => expandType(tp2) match {
              case TupleType(ts2)
                => ts1.length == ts2.length &&
                   (ts1 zip ts2).map{ case (t1,t2) => typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case _
        => tp2 match {
             case NamedType(n) => typeEquivalence(tp1,expandType(tp2))
             case _ => false
           }
    }

  /* tracing level */
  var level: Int = -1

  /** trace typechecking */
  def trace[T] ( e: Any, result: => T ): T = {
    if (trace_typecheck) {
       level += 1
       println(" "*(3*level)+"** "+e)
    }
    val res = result
    if (trace_typecheck) {
       print(" "*(3*level))
       if (e.isInstanceOf[Stmt] || e.isInstanceOf[Definition])
          println("->")
       else println("-> "+res)
       level -= 1
    }
    res
  }

  /** typecheck an expression AST */
  def typecheck ( e: Expr ): Type =
    trace(e,e match {
      case BinOpExp(op,l,r)
        => val ltp = typecheck(l)
           val rtp = typecheck(r)
           if (!typeEquivalence(ltp,rtp))
              error("Incompatible types in binary operation: "+e)
           else if (op.equals("and") || op.equals("or"))
                   if (typeEquivalence(ltp,BooleanType()))
                      ltp
                   else error("AND/OR operation can only be applied to booleans: "+e)
           else if (op.equals("eq") || op.equals("neq"))
                   BooleanType()
           else if (!typeEquivalence(ltp,IntType()) && !typeEquivalence(ltp,FloatType()))
                   error("Binary arithmetic operations can only be applied to integer or real numbers: "+e)
           else if (op.equals("gt") || op.equals("lt") || op.equals("geq") || op.equals("leq"))
                   BooleanType()
           else ltp

      /* PUT YOUR CODE HERE */
      case UnOpExp (op, er)
        => val etp = typecheck(er)
           if (op.equals("not"))
              if(typeEquivalence(etp, BooleanType()))
                 etp
              else error("NOT operation can only be applied to booleans: "+e)
           else if (op.equals("minus"))
              if(typeEquivalence(etp, IntType()) || typeEquivalence(etp, FloatType()))
                 etp
              else error("UMINUS operation can only be applied to Int or Float: "+e)
           else error("Not a unary op")

      case IntConst (v) 
        => IntType()

      case FloatConst (v) 
        => FloatType()

      case StringConst (v)
        => StringType()

      case BooleanConst (v)
        => BooleanType()

      case LvalExp (lv)
        => typecheck(lv)

      case CallExp(nm, es)
        => st.lookup(nm) match {
              case Some(FuncDeclaration(ot, ps, _, _, _))
                => { if (ps.size != es.size) {
                        error("Number of formal parameters does not much the number of arguments in call: "+e)
                     }
                     var ls = (es zip ps).map{case (e, Bind (v, tp))
                  => if (!typeEquivalence(typecheck(e), tp))
                        error("Typechecking Error: The type of call argument ("+tp+") does not match the type of the formal parameter: "+typecheck(e))
                     else ot }
                   ot}
              case Some(_) => error(nm+" is not a function")
              case None => error("Undefined function name: "+nm)
        }

      case ArrayExp(es)
        => val tp = typecheck(es.head)
           if (!es.tail.forall(x => typeEquivalence(typecheck(x), tp))) { error("The mismatch type error in array: "+e) }
           ArrayType(tp)

      case ArrayGen(e1, e2)
        => if (!typeEquivalence(typecheck(e1), IntType())) {
              error("The array length must be integer: "+e)
           }
           ArrayType(typecheck(e2))

      case RecordExp(el)
        => val rec = el.map{case (Bind (nm, e))
          => Bind (nm, typecheck(e)) }
           RecordType(rec)

      case TupleExp(es)
        => val ls = es.map{ x => typecheck(x) }
           TupleType(ls)

      case NullExp()
        => AnyType()

      case _ => throw new Error("Wrong expression: "+e)
    } )

  /** typecheck an Lvalue AST */
  def typecheck ( e: Lvalue ): Type =
    trace(e,e match {
      case Var(name)
        => st.lookup(name) match {
              case Some(VarDeclaration(t,_,_)) => t
              case Some(_) => error(name+" is not a variable")
              case None => error("Undefined variable: "+name)
        }

      /* PUT YOUR CODE HERE */
      case ArrayDeref(lv, ex)
        => val etp = typecheck(ex)
           val lvtp = typecheck(lv)
           lvtp match {
              case ArrayType(t1)
                => t1
              case _
                => error("Name "+lv+" does not reference an array")
           }
           
      case RecordDeref(rec, att)
        => val rctp = typecheck(rec)
           rctp match {
              case RecordType(el)
                => val ntp = el.find(x => x match {
                     case Bind(nm, tp)
                       => (nm == att)
                     case _ => false
                     } )
                   ntp match {
                     case Some(Bind(nm, tp)) => tp
                     case _ => error("Record does not contain "+att+ "at "+e)
                   }
             
              case NamedType(nm)
                => st.lookup(nm) match {
                  case Some(TypeDeclaration(etp))
                   //val etp = expandType(rctp)
                   //etp
                     => etp match {
                      case RecordType(el)
                        => val ntp = el.find(x => x match {
                           case Bind(nm, tp)
                             => (nm == att)
                             case _ => false
                           } )
                           ntp match {
                              case Some(Bind(nm, tp)) => tp
                              case _ => error("Record does not contain "+att+ "at "+e)

                         
                           }
                      case _
                        => error("That record does not exist "+e)
                   }
                   case _
                     => error ("That named type does not exist"+e)  
                }

              case _
                => error("That record does not exist "+e)
           }
 
      case _ => throw new Error("Wrong lvalue: "+e)
    } )

  /** typecheck a statement AST using the expected type of the return value from the current function */
  def typecheck ( e: Stmt, expected_type: Type ) {
    trace(e,e match {
      case AssignSt(d,s)
        => if (!typeEquivalence(typecheck(d),typecheck(s)))
              error("Incompatible types in assignment: "+e)
           //else typecheck(d)

      /* PUT YOUR CODE HERE */
      case PrintSt(es)
        => es.foreach(typecheck(_))

      case ReadSt(es)
         => es.foreach(typecheck(_))

      case BlockSt(dl, sl)
         => st.begin_scope()
            dl.foreach{ typecheck(_) }
            sl.foreach{ typecheck(_, AnyType()) }
            st.end_scope()

      case IfSt(e, then_st, else_st)
         => val etp = typecheck(e)
            if (!typeEquivalence(etp, BooleanType())) {
               error("If condition must be boolean: "+e)
            }
            typecheck(then_st, AnyType())
            if (else_st != null) {
                typecheck(else_st, AnyType())
            }

      case ReturnValueSt(e)
        => typecheck(e)

      case ReturnSt()
        => 

      case ExitSt()
        =>

      case WhileSt(cnd, bd)
        => if (!typeEquivalence(typecheck(cnd), BooleanType())) {
              error("Expected a boolean in WHILE test: "+e)
           }
           typecheck(bd, AnyType())

      case CallSt(nm, es)
        => st.lookup(nm) match {
              case Some(FuncDeclaration(ot, ps, _, _, _))
                => { if (ps.size != es.size) {
                        error("Number of formal parameters does not much the number of arguments in call: "+e)
                     }
                     var ls = (es zip ps).map{case (e, Bind (v, tp))
                  => if (!typeEquivalence(typecheck(e), tp))
                        error("Typechecking Error: The type of call argument ("+tp+") does not match the type of the formal parameter: "+typecheck(e))
                     else ot }
                   ot}
              case Some(_) => error(nm+" is not a function")
              case None => error("Undefined function name: "+nm)
        }

      case ForSt(nm, init, step, incr, bd)
        => st.begin_scope()
           st.insert(nm, VarDeclaration(IntType(),0,0))
           if (!typeEquivalence(typecheck(init), IntType())) {
              error("initial value in FOR loop must be integer: "+e)
           }
           if (!typeEquivalence(typecheck(step), IntType())) {
              error("step in FOR loop must be integer: "+e)
           }
           if (!typeEquivalence(typecheck(incr), IntType())) {
              error("final value in FOR loop must be integer: "+e)
           }

           typecheck(bd, AnyType())
           st.end_scope()

      case LoopSt(st)
        => typecheck(st, AnyType())

      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck a definition */
  def typecheck ( e: Definition ) {
    trace(e,e match {
      case FuncDef(f,ps,ot,b)
        => st.insert(f,FuncDeclaration(ot,ps,"",0,0))
           st.begin_scope()
           ps.foreach{ case Bind(v,tp) => st.insert(v,VarDeclaration(tp,0,0)) }
           typecheck(b,ot)
           st.end_scope()

      /* PUT YOUR CODE HERE */
      case VarDef(nm, tp, e)
        => val etp = typecheck(e)
           if (typeEquivalence(etp, tp)) {
              if (tp.isInstanceOf[AnyType])
                st.insert(nm,VarDeclaration(etp, 0, 0))
              else
                st.insert(nm,VarDeclaration(tp, 0, 0))
           }
           else error("Right hand type does not match "+tp+" as specified")

      case (TypeDef(nm, tp))
        => st.insert(nm, TypeDeclaration(tp))

      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck the main program */
  def typecheck ( e: Program ) {
    typecheck(e.body,NoType())
  }
}
