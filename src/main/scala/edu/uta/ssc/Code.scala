/*
 * Copyright © 2023 University of Texas at Arlington
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package edu.uta.ssc

object CodeGenerator {
  import TypeChecker._

  /** global declarations */
  var declarations: List[Bind[IRdecl]] = Nil

  def lookup ( name: String ): Option[IRdecl] = {
    declarations.foreach {
      case Bind(nm,d)
        => if (nm==name)
             return Some(d)
    }
    None
  }

  var name_counter = 0

  /** generate a new name */
  def new_name ( name: String ): String = {
    name_counter += 1
    name + "_" + name_counter
  }

  /** return the type name of the current frame */
  def frame_type_name ( fname: String ): String =
    st.lookup(fname) match {
      case Some(FuncDeclaration(_,_,label,_,_))
        => label+"_frame"
      case _ => throw new Error("Unknown frame for function "+fname)
    }

  /** true if tp1 occurs inside tp2 */
  def occurs ( tp1: Type, tp2: Type ): Boolean =
    tp2 match {
      case TupleType(ts)
        => ts.map(occurs(tp1,_)).reduce(_ || _)
      case RecordType(rs)
        => rs.map{ case Bind(_,etp) => occurs(tp1,etp) }.reduce(_ || _)
      case ArrayType(etp)
        => occurs(tp1,etp)
      case _ => tp1 == tp2
    }

  /** Data Allocation: convert a type AST to an IR type */
  def Type2IRtype ( tp: Type ): IRtype =
    tp match {
      case IntType()
        => IntIRtype()
      case FloatType()
        => FloatIRtype()
      case BooleanType()
        => BooleanIRtype()
      case StringType()
        => StringIRtype()
      case NoType()
        => VoidIRtype()
      case AnyType()
        => VoidIRtype()
      case NamedType(n)
        => lookup(n) match {
             case Some(IRtypeDecl(lnm,_))
               => AddressIRtype(NamedIRtype(lnm))
             case _
               => st.lookup(n) match {
                    case Some(TypeDeclaration(ht))
                      => if (occurs(tp,ht)) {
                           // store the new recursive type in the declarations
                           val lnm = new_name(n)
                           val bd: Bind[IRdecl] = Bind(n,IRtypeDecl(lnm,null))
                           declarations = declarations :+ bd
                           Type2IRtype(ht) match {
                             case AddressIRtype(etp)
                               => bd.value = IRtypeDecl(lnm,etp)
                                  AddressIRtype(NamedIRtype(lnm))
                             case _ => throw new Error("Wrong recursive type: "+n)
                           }
                         } else Type2IRtype(ht)
                    case _ => throw new Error("Undefined type: "+n)
                    }
           }
      case ArrayType(etp)
        => AddressIRtype(TupleIRtype(List(IntIRtype(),
                                          VecIRtype(Type2IRtype(etp)))))
      case TupleType(ltp)
        => AddressIRtype(TupleIRtype(ltp.map(Type2IRtype)))
      case RecordType(bs)
        => AddressIRtype(TupleIRtype(bs.map{ case Bind(_,etp) => Type2IRtype(etp) }))
      case FunctionType(fs,ot)
        => val ftp = FunctionIRtype(AddressIRtype(ByteIRtype())::fs.map(Type2IRtype),
                                    Type2IRtype(ot))
           // a closure is a pair of a function type with a static link type (a void* type)
           AddressIRtype(TupleIRtype(List(AddressIRtype(ftp),
                                          AddressIRtype(ByteIRtype()))))
      case _ => throw new Error("Uknown type: "+tp)
    }

  /** allocate a new variable at the end of the current frame and return its value */
  def allocate_in_frame ( name: String, var_type: Type, fname: String ): IRexp =
    st.lookup(fname) match {
      case Some(FuncDeclaration(rtp,params,label,level,min_offset))
        => // allocate variable at the next available offset in frame
           st.insert(name,VarDeclaration(var_type,level,min_offset))
           // update the next available offset in frame
           st.replace(fname,FuncDeclaration(rtp,params,label,level,min_offset+1))
           // return the code that accesses the variable
           Mem(Indexed(FramePointer(),IntValue(min_offset)))
      case _ => throw new Error("No current function: " + fname)
    }

  /** return the address of a frame-allocated variable from the run-time stack */
  def access_variable ( name: String, level: Int, fname: String ): IRexp =
    st.lookup(name) match {
      case Some(VarDeclaration(_,var_level,offset))
        => var sl: IRexp = FramePointer()
           // non-local variable: follow the static link (level-var_level) times
           for ( _ <- var_level+1 to level )
             sl = Mem(Indexed(sl,IntValue(0)))
           Indexed(sl,IntValue(offset))
      case Some(FuncDeclaration(rtp,params,label,flevel,_))
        => var sl: IRexp = FramePointer()
           // non-local variable: follow the static link (level-var_level) times
           for ( _ <- flevel+1 to level )
             sl = Mem(Indexed(sl,IntValue(0)))
           // construct a closure
           val ftp = FunctionType(params.map(_.value),rtp)
           val C = allocate_in_frame("C",ftp,fname)
           ESeq(Move(C,Closure(label,sl)),
                access_variable("C",level,fname))
      case _ => throw new Error("Undefined variable: " + name)
    }

  /** return the IR code from the Expr e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Expr, level: Int, fname: String ): IRexp =
    e match {
      case IntConst(n)
        => IntValue(n)
      case FloatConst(n)
        => FloatValue(n)
      case StringConst(n)
        => StringValue(n)
      case NullExp()
        => NullValue()
      case BooleanConst(b)
        => BooleanValue(b)
      case BinOpExp(op,left,right)
        => val cl = code(left,level,fname)
           val cr = code(right,level,fname)
           val nop = op.toUpperCase()
           Binop(nop,cl,cr)
      case UnOpExp(op,u)
        => val c = code(u,level,fname)
           val nop = op.toUpperCase()
           Unop(nop,c)
      case LvalExp(v)
        => Mem(code(v,level,fname))
      case CallExp(f,args)
        => st.lookup(f) match {
             case Some(FuncDeclaration(_,_,label,callee_level,_))
               => var sl: IRexp = FramePointer()
                  for ( _ <- callee_level to level )
                     sl = Mem(Indexed(sl,IntValue(0)))
                  Call(Address(label),sl,args.map(code(_,level,fname)))
             case Some(VarDeclaration(FunctionType(_,_),_,_))
               => val cv = access_variable(f,level,fname)
                  /* get the function address and the frame link from the closure cv */
                  Call(Mem(cv),
                       Mem(Indexed(cv,IntValue(1))),  // frame link
                       args.map(code(_,level,fname)))
             case _ => throw new Error("Unkown function: "+f)
           }
      case TupleExp(cl)
        => val tp = typecheck(e)
           val ltp = Type2IRtype(tp).asInstanceOf[AddressIRtype].address
           val T = allocate_in_frame(new_name("T"),tp,fname)
           val cs = cl.zipWithIndex.map {
                       case (u,i) => Move(Mem(Indexed(T,IntValue(i))),
                                          code(u,level,fname))
                    }
           ESeq(Seq(Move(T,Allocate(ltp,TypeSize(ltp)))::cs),T)
      case RecordExp(cl)
        => val tp = typecheck(e)
           val ltp = Type2IRtype(tp).asInstanceOf[AddressIRtype].address
           val R = allocate_in_frame(new_name("R"),typecheck(e),fname)
           val cs = cl.zipWithIndex.map {
                       case (Bind(_,u),i) => Move(Mem(Indexed(R,IntValue(i))),
                                                  code(u,level,fname))
                    }
           ESeq(Seq(Move(R,Allocate(ltp,TypeSize(ltp)))::cs),R)
      case ArrayExp(cl)
        => val tp = typecheck(cl.head)
           val ltp = Type2IRtype(tp)
           val A = allocate_in_frame(new_name("A"),typecheck(e),fname)
           val cs = cl.zipWithIndex.map {
                       case (u,i) => Move(Mem(Indexed(Indexed(A,IntValue(1)),
                                                    IntValue(i))),
                                          code(u,level,fname))
                    }
           ESeq(Seq(Move(A,Allocate(TupleIRtype(List(IntIRtype(),VecIRtype(ltp))),
                                    Binop("PLUS",TypeSize(IntIRtype()),
                                          Binop("TIMES",TypeSize(Type2IRtype(tp)),
                                                IntValue(cl.size)))))::
                    Move(Mem(Indexed(A,IntValue(0))),
                         IntValue(cl.length))::cs),A)
      case ArrayGen(len,v)
        => val tp = typecheck(v)
           val ltp = Type2IRtype(tp)
           val A = allocate_in_frame(new_name("A"),ArrayType(tp),fname)
           val L = allocate_in_frame(new_name("L"),IntType(),fname)
           val V = allocate_in_frame(new_name("V"),tp,fname)
           val I = allocate_in_frame(new_name("I"),IntType(),fname)
           val loop = new_name("Loop")
           val exit = new_name("Exit")
           ESeq(Seq(List(Move(L,code(len,level,fname)),        // store length in L
                         Move(A,Allocate(TupleIRtype(List(IntIRtype(),VecIRtype(ltp))),
                                         Binop("PLUS",TypeSize(IntIRtype()),
                                               Binop("TIMES",TypeSize(Type2IRtype(tp)),L)))),
                         Move(V,code(v,level,fname)),          // store value in V
                         Move(Mem(Indexed(A,IntValue(0))),L),  // store length in A[0]
                         Move(I,IntValue(0)),
                         Label(loop),                          // for-loop
                         CJump(Binop("GEQ",I,L),exit),
                         Move(Mem(Indexed(Indexed(A,IntValue(1)),I)),V),    // A[i] = v
                         Move(I,Binop("PLUS",I,IntValue(1))),
                         Jump(loop),
                         Label(exit))),
                A)
      case FunctionExp(fs,rtp,body)
        => val lname = new_name("lambda")
           /* create a closure for the anonymous function: it contains the function address
              and a pointer to the current frame */
           code(FuncDef(lname,fs,rtp,body),fname,level)
           st.lookup(lname) match {
             case Some(FuncDeclaration(_,_,flabel,_,_))
               => Closure(flabel,FramePointer())
             case _ => throw new Error("Unkown function: "+e)
           }
        }

  /** return the IR code from the address of the Lvalue e (level is the current
   *  function nesting level, fname is the name of the current function/procedure) */
  def code ( e: Lvalue, level: Int, fname: String ): IRexp =
    e match {
      case Var(s)
        => access_variable(s,level,fname)
      case ArrayDeref(v,u)
        => val cv = code(v,level,fname)
           val cu = code(u,level,fname)
           Indexed(Indexed(Mem(cv),IntValue(1)),cu)
      case TupleDeref(t,i)
        => val ct = code(t,level,fname)
           Indexed(Mem(ct),IntValue(i))
      case RecordDeref(r,a)
        => val cr = code(r,level,fname)
           expandType(typecheck(r)) match {
              case RecordType(cl)
                => val i = cl.map(_.name).indexOf(a)
                   Indexed(Mem(cr),IntValue(i))
              case ArrayType(etp) if a == "length"
                => Indexed(Mem(cr),IntValue(0))
              case _ => throw new Error("Unkown record: "+e)
           }
    }

  /** return the IR code from the Statement e (level is the current function nesting level,
   *  fname is the name of the current function/procedure)
   *  and exit_label is the exit label       */
  def code ( e: Stmt, level: Int, fname: String, exit_label: String ): IRstmt =
    e match {
      case AssignSt(v,u)
        => val cd = code(v,level,fname)
           val cs = code(u,level,fname)
           Move(Mem(cd),cs)
      case CallSt(f,args)
        => st.lookup(f) match {
             case Some(FuncDeclaration(_,_,label,callee_level,_))
               => var sl: IRexp = FramePointer()
                  for ( _ <- callee_level to level )
                     sl = Mem(Indexed(sl,IntValue(0)))
                  CallP(Address(label),sl,args.map(code(_,level,fname)))
             case Some(VarDeclaration(FunctionType(_,_),_,_))
               => val cv = access_variable(f,level,fname)
                  /* get the function address and the frame link from the closure cv */
                  CallP(Mem(cv),
                        Mem(Indexed(cv,IntValue(1))),   // frame link
                        args.map(code(_,level,fname)))
             case _ => throw new Error("Unkown function: "+f)
           }
      case ReadSt(el)
        => Seq(el.map(v => {
                  val cv = code(v,level,fname)
                  typecheck(v) match {
                     case IntType()
                       => SystemCall("READ_INT",cv)
                     case FloatType()
                       => SystemCall("READ_FLOAT",cv)
                     case StringType()
                       => SystemCall("READ_STRING",cv)
                     case tp => throw new Error("*** Unknown type "+tp)
                  }
               }))
      case PrintSt(el)
        => val cs = el.map(v => {
                   val cv = code(v,level,fname)
                   typecheck(v) match {
                      case IntType() => SystemCall("WRITE_INT",cv)
                      case FloatType() => SystemCall("WRITE_FLOAT",cv)
                      case StringType() => SystemCall("WRITE_STRING",cv)
                      case tp => throw new Error("*** Unknown type "+tp)
                   }
                })
           Seq(cs :+ SystemCall("WRITE_STRING",StringValue("\\n")))
      case IfSt(p,a,b)
        => val cont = new_name("Cont")
           val exit = new_name("Exit")
           val cp = code(p,level,fname)
           val ca = code(a,level,fname,exit)
           val cb = if (b == null) Seq(List()) else code(b,level,fname,exit)
           Seq(List(CJump(cp,exit),
                    cb,
                    Jump(cont),
                    Label(exit),
                    ca,
                    Label(cont)))
      case WhileSt(p,s)
        => val loop = new_name("Loop")
           val exit = new_name("Exit")
           val cp = code(p,level,fname)
           val cs = code(s,level,fname,exit)
           Seq(List(Label(loop),
                    CJump(Unop("NOT",cp),exit),
                    cs,
                    Jump(loop),
                    Label(exit)))
      case LoopSt(s)
        => val loop = new_name("Loop")
           val exit = new_name("Exit")
           val cs = code(s,level,fname,exit)
           Seq(List(Label(loop),
                    cs,
                    Jump(loop),
                    Label(exit)))
      case ForSt(v,a,b,c,s)
        => val loop = new_name("Loop")
           val exit = new_name("Exit")
           val cv = allocate_in_frame(v,IntType(),fname)
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
      case ExitSt()
        => Jump(exit_label)
      case ReturnValueSt(u)
        => Return(code(u,level,fname))
      case ReturnSt()
        => Return(VoidValue())
      case BlockSt(dl)
        => Seq(dl.map{ case Left(d) => code(d,fname,level)
                       case Right(s) => code(s,level,fname,exit_label) })
      case _ => throw new Error("*** Unknown AST: " + e)
    }

  /** return the IR code for the declaration block of function fname
   * (level is the current function nesting level) */
  def code ( e: Definition, fname: String, level: Int ): IRstmt =
    e match {
      case TypeDef(n,tp)
        => st.insert(n,TypeDeclaration(tp))
           Seq(List())
      case VarDef(v,AnyType(),u)
        => val V = allocate_in_frame(v,typecheck(u),fname)
           Move(V,code(u,level,fname))
      case VarDef(v,tp,u)
        => val V = allocate_in_frame(v,tp,fname)
           Move(V,code(u,level,fname))
      case FuncDef(f,ps,ot,b)
        => val flabel = if (f == "main") f else new_name(f)
           st.insert(f,FuncDeclaration(ot,ps,flabel,level+1,
                                       if (f == "main") 0 else ps.length+1))
           st.begin_scope()
           /* allocate formal parameters in the frame */
           ps.zipWithIndex.foreach {
              case (Bind(v,tp),i)
                => st.insert(v,VarDeclaration(tp,level+1,i+1))
           }
           /** remove all Seq and ESeq from the function body */
           val body = Normalizer.normalize(code(b,level+1,f,""))
           /** get the types of all local variables ordered by their offset */
           val local_var_types = st.current_scope().flatMap {
                                    case (_,VarDeclaration(tp,_,_)) => List(tp)
                                    case _ => Nil
                                 }.reverse
           val frame_types = if (f == "main")
                                local_var_types.map(Type2IRtype)
                             else AddressIRtype(NamedIRtype(frame_type_name(fname)))::
                                      local_var_types.map(Type2IRtype)
           val formals = ps.map{ case Bind(_,tp) => Type2IRtype(tp) }
           st.end_scope()
           declarations = declarations :+
                              Bind(f,IRfuncDecl(flabel,frame_types,formals,
                                                Type2IRtype(ot),level+1,body)
                                            .asInstanceOf[IRdecl]) :+
                              Bind(flabel+"_frame",
                                   IRtypeDecl(flabel+"_frame",
                                              TupleIRtype(frame_types)).asInstanceOf[IRdecl])
           Seq(List())
    }

    def code ( e: Program ): List[Bind[IRdecl]] =
      e match {
        case Program(b@BlockSt(_))
          => declarations = Nil
             st.begin_scope()
             code(FuncDef("main",List(),NoType(),b),"",0)
             st.end_scope()
             declarations
        case _ => throw new Error("Wrong program "+e);
      }
}
