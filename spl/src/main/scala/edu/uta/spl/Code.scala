/****************************************************************************************************
 *
 * File: Code.scala
 * The IR code generator for SPL programs
 *
 ****************************************************************************************************/

package edu.uta.spl
import scala.collection.mutable.ListBuffer

abstract class CodeGenerator ( tc: TypeChecker )  {
  def typechecker: TypeChecker = tc
  def st: SymbolTable = tc.st
  def code ( e: Program ): IRstmt
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp
}


class Code ( tc: TypeChecker ) extends CodeGenerator(tc) {

  var name_counter = 0

  /** generate a new name */
  def new_name ( name: String ): String = {
    name_counter += 1
    name + "_" + name_counter
  }

  /** IR code to be added at the end of program */
  var addedCode: List[IRstmt] = Nil

  def addCode ( code: IRstmt* ) {
    addedCode ++= code
  }

  /** allocate a new variable at the end of the current frame and return the access code */
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp =
    st.lookup(fname) match {
      case Some(FuncDeclaration(rtp,params,label,level,min_offset))
        => // allocate variable at the next available offset in frame
           st.insert(name,VarDeclaration(var_type,level,min_offset))
           // the next available offset in frame is 4 bytes below
           st.replace(fname,FuncDeclaration(rtp,params,label,level,min_offset-4))
           // return the code that accesses the variable
           Mem(Binop("PLUS",Reg("fp"),IntValue(min_offset)))
      case _ => throw new Error("No current function: " + fname)
    }

  /** access a frame-allocated variable from the run-time stack */
  def access_variable ( name: String, level: Int ): IRexp =
    st.lookup(name) match {
      case Some(VarDeclaration(_,var_level,offset))
        => var res: IRexp = Reg("fp")
           // non-local variable: follow the static link (level-var_level) times
           for ( i <- var_level+1 to level )
               res = Mem(Binop("PLUS",res,IntValue(-8)))
           Mem(Binop("PLUS",res,IntValue(offset)))
      case _ => throw new Error("Undefined variable: " + name)
    }

  /** return the IR code from the Expr e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Expr, level: Int, fname: String ): IRexp =
    e match {
      case BinOpExp(op,left,right)
        => val cl = code(left,level,fname)
           val cr = code(right,level,fname)
           val nop = op.toUpperCase()
           Binop(nop,cl,cr)
      case ArrayGen(len,v)
        => val A = allocate_variable(new_name("A"),typechecker.typecheck(e),fname)
           val L = allocate_variable(new_name("L"),IntType(),fname)
           val V = allocate_variable(new_name("V"),typechecker.typecheck(v),fname)
           val I = allocate_variable(new_name("I"),IntType(),fname)
           val loop = new_name("loop")
           val exit = new_name("exit")
           ESeq(Seq(List(Move(L,code(len,level,fname)),   // store length in L
                         Move(A,Allocate(Binop("PLUS",L,IntValue(1)))),
                         Move(V,code(v,level,fname)),     // store value in V
                         Move(Mem(A),L),                  // store length in A[0]
                         Move(I,IntValue(0)),
                         Label(loop),                     // for-loop
                         CJump(Binop("GEQ",I,L),exit),
                         Move(Mem(Binop("PLUS",A,Binop("TIMES",Binop("PLUS",I,IntValue(1)),IntValue(4)))),V),  // A[i] = v
                         Move(I,Binop("PLUS",I,IntValue(1))),
                         Jump(loop),
                         Label(exit))),
                A)

      /* PUT YOUR CODE HERE */

      case UnOpExp(op, ex)
        => val cex = code(ex, level, fname)
           val nop = op.toUpperCase()
           Unop(nop, cex)

      case IntConst (v) 
        => IntValue(v)

      case FloatConst (v) 
        => FloatValue(v)

      case StringConst (v)
        => StringValue(v)

      case BooleanConst (v)
        => if (v)
              IntValue(1)
           else
              IntValue(0)

      case ArrayExp(es)
        => var el = new ListBuffer[Move]()
           val A = allocate_variable(new_name("A"),typechecker.typecheck(e),fname)
           val L = allocate_variable(new_name("L"),IntType(),fname)
           var i = 1;
           el += Move(L,Allocate(code(new IntConst(es.size+1),level,fname)))
           el += Move(Mem(A), new IntValue(es.size))
           es.foreach(x => {
              el += Move(Mem(Binop("PLUS",A,new IntValue(i*4))),code(x,level,fname))
              i += 1
           } )

           ESeq(Seq(el.toList), A)

      case LvalExp(v)
        => code(v, level, fname)

      case RecordExp(es)
        => var el = new ListBuffer[Move]()
           val A = allocate_variable(new_name("A"),typechecker.typecheck(e),fname)
           val L = allocate_variable(new_name("L"),IntType(),fname)
           var i = 0;
           el += Move(L,Allocate(code(new IntConst(es.size),level,fname)))
           val eb = es.map{ case (Bind (nm, e))
             => el += Move(Mem(Binop("PLUS",A,new IntValue(i*4))),code(e,level,fname))
              i += 1
           }

           ESeq(Seq(el.toList), A)

      case CallExp(nm, ex)
        => val el = ex.map{ x =>
                    code(x, level, fname) }
          
           st.lookup(nm) match {
           case Some(FuncDeclaration(_,_,lbl,var_level,offset))
             => var res: IRexp = Reg("fp")

                for ( i <- var_level to level )
                   res = Mem(Binop("PLUS",res,IntValue(-8)))
                
                Call(lbl, res, el)

                case _ => throw new Error("Undefined function: " + nm)
                }

      case NullExp()
        => IntValue(0) 

      case _ => throw new Error("Wrong expression: "+e)
    }

  /** return the IR code from the Lvalue e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Lvalue, level: Int, fname: String ): IRexp =
    e match {
     case RecordDeref(r,a)
        => val cr = code(r,level,fname)
           typechecker.expandType(typechecker.typecheck(r)) match {
              case RecordType(cl)
                => val i = cl.map(_.name).indexOf(a)
                   Mem(Binop("PLUS",cr,IntValue(i*4)))
              case _ => throw new Error("Unkown record: "+e)
           }

     /* PUT YOUR CODE HERE */

     case Var(nm)
       => access_variable(nm, level)

     case ArrayDeref(a, ex)
       => val ca = code(a, level, fname)
          val cex = code(ex, level, fname)
          typechecker.expandType(typechecker.typecheck(a)) 
match {
             case ArrayType(cl)
               => Mem(Binop("PLUS",ca,Binop("TIMES", Binop("PLUS", cex, IntValue(1)), IntValue(4))))

             case _ => throw new Error("Unknown array: "+e)
         }

     case _ => throw new Error("Wrong statement: " + e)
    }

  /** return the IR code from the Statement e (level is the current function nesting level,
   *  fname is the name of the current function/procedure)
   *  and exit_label is the exit label       */
  def code ( e: Stmt, level: Int, fname: String, exit_label: String ): IRstmt =
    e match {
      case ForSt(v,a,b,c,s)
        => val loop = new_name("loop")
           val exit = new_name("exit")
           val cv = allocate_variable(v,IntType(),fname)
           val ca = code(a,level,fname)
           val cb = code(b,level,fname)
           val cc = code(c,level,fname)
           val cs = code(s,level,fname,exit)
           Seq(List(Move(cv,ca),  // needs cv, not Mem(cv)
                    Label(loop),
                    CJump(Binop("GT",cv,cb),exit),
                    cs,
                    Move(cv,Binop("PLUS",cv,cc)),  // needs cv, not Mem(cv)
                    Jump(loop),
                    Label(exit)))

      /* PUT YOUR CODE HERE */

      case BlockSt(dl, sl)
        => st.begin_scope()
           val dc = dl.map{d => code(d, fname, level)}
           val sc = sl.map{s => code(s, level, fname, exit_label)}
           val cd = dc ++ sc
           st.end_scope()
           Seq(cd)

      case PrintSt(es)
        => val etp = es.zip(es.map{e => typechecker.typecheck(e)})
           var pl = new ListBuffer[SystemCall]()

           for ( (ex, tp) <- es zip es.map{e => typechecker.typecheck(e)} ) {
              if (tp == IntType()) {
                 pl += SystemCall("WRITE_INT", code(ex, level, fname))
              }
              if (tp == FloatType()) {
                 pl += SystemCall("WRITE_FLOAT", code(ex, level, fname))
              }
              if (tp == StringType()) {
                 pl += SystemCall("WRITE_STRING", code(ex, level, fname))
              }
              if (tp == BooleanType()) {
                 pl += SystemCall("WRITE_BOOL", code(ex, level, fname))
              }
           }
           pl += SystemCall("WRITE_STRING", code(StringConst("\\n"), level, fname))
           Seq(pl.toList)

      case AssignSt(dest, src)
        => Move(code(dest, level, fname), code(src, level, fname))

      case WhileSt(ex, st)
        => val loop = new_name("loop")
           val exit = new_name("exit")
           Seq(List(Label(loop),
                    CJump(Unop("NOT", code(ex, level, fname)), exit),
                    code(st, level, fname, exit_label),
                    Jump(loop),
                    Label(exit)))

      case IfSt(ex, then_st, else_st)
        => val cont = new_name("cont")
           val exit = new_name("exit")

           if (else_st != null) {
              Seq(List(CJump(code(ex, level, fname), exit),
                       code(else_st, level, fname, exit_label),
                       Jump(cont),
                       Label(exit),
                       code(then_st, level, fname, exit_label)))                       
            }
            else {
              Seq(List(CJump(code(ex, level, fname), exit),
                       Seq(List()),
                       Jump(cont),
                       Label(exit),
                       code(then_st, level, fname, exit_label),
                       Label(cont)))
            }

      case CallSt(nm, ex)
        => val el = ex.map{ x =>
                    code(x, level, fname) }
          
           st.lookup(nm) match {
           case Some(FuncDeclaration(_,_,lbl,var_level,offset))
             => var res: IRexp = Reg("fp")
         
                for ( i <- var_level to level )
                   res = Mem(Binop("PLUS",res,IntValue(-8)))
                
                CallP(lbl, res, el)

                case _ => throw new Error("Undefined function: " + nm)
                }

      case ReturnValueSt(ex)
        => Seq(List(Move(Reg("a0"), code(ex, level, fname)),
               Move(Reg("ra"), Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
               Move(Reg("sp"), Reg("fp")),
               Move(Reg("fp"), Mem(Reg("fp"))),
               Return()))

      case ReturnSt()
        => Seq(List(Move(Reg("ra"), Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
               Move(Reg("sp"), Reg("fp")),
               Move(Reg("fp"), Mem(Reg("fp"))),
               Return()))

      case ReadSt(es)
        => val etp = es.zip(es.map{e => typechecker.typecheck(e)})
           var pl = new ListBuffer[SystemCall]()

           for ( (ex, tp) <- es zip es.map{e => typechecker.typecheck(e)} ) {
              if (tp == IntType()) {
                 pl += SystemCall("READ_INT", code(ex, level, fname))
              }
              if (tp == FloatType()) {
                 pl += SystemCall("READ_FLOAT", code(ex, level, fname))
              }
           }
           Seq(pl.toList)

      case ExitSt()
        => Jump(exit_label)

      case _ => throw new Error("Wrong statement: " + e)
   }

  /** return the IR code for the declaration block of function fname
   * (level is the current function nesting level) */
  def code ( e: Definition, fname: String, level: Int ): IRstmt =
    e match {
      case FuncDef(f,ps,ot,b)
        => val flabel = if (f == "main") f else new_name(f)
           /* initial available offset in frame f is -12 */
           st.insert(f,FuncDeclaration(ot,ps,flabel,level+1,-12))
           st.begin_scope()
           /* formal parameters have positive offsets */
           ps.zipWithIndex.foreach{ case (Bind(v,tp),i)
                                      => st.insert(v,VarDeclaration(tp,level+1,(ps.length-i)*4)) }
           val body = code(b,level+1,f,"")
           st.end_scope()

           st.lookup(f) match {
             case Some(FuncDeclaration(_,_,_,_,offset))
               => addCode(Label(flabel),
                          /* prologue */
                          Move(Mem(Reg("sp")),Reg("fp")),
                          Move(Reg("fp"),Reg("sp")),
                          Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-4))),Reg("ra")),
                          Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-8))),Reg("v0")),
                          Move(Reg("sp"),Binop("PLUS",Reg("sp"),IntValue(offset))),
                          body,
                          /* epilogue */
                          Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
                          Move(Reg("sp"),Reg("fp")),
                          Move(Reg("fp"),Mem(Reg("fp"))),
                          Return())
                  Seq(List())
             case _ => throw new Error("Unkown function: "+f)
           }

      /* PUT YOUR CODE HERE */
      case VarDef(nm, tp, va)
        => if(tp.isInstanceOf[AnyType]) {
              Move(allocate_variable ( nm, typechecker.typecheck(va), fname ), code(va, level, fname))
           }
           else {
              Move(allocate_variable ( nm, tp, fname ), code(va, level, fname))
           }

      case TypeDef(nm, tp)
        => st.insert(nm, TypeDeclaration(tp))
           Seq(List())

      case _ => throw new Error("Wrong statement: " + e)
    }

    def code ( e: Program ): IRstmt =
      e match {
        case Program(b@BlockSt(_,_))
          => st.begin_scope()
             val res = code(FuncDef("main",List(),NoType(),b),"",0)
             st.end_scope()
             Seq(res::addedCode)

        case _ => throw new Error("Wrong program "+e);
      }
}
