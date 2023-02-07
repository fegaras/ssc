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


/* Generates LLVM code from IR code */
class LLVM ( out: java.io.PrintStream ) {
  /** contains all the function and type declarations */
  var declarations: List[Bind[IRdecl]] = Nil

  /** contains global LLVM constants (currently strings only) */
  var globals: List[String] = Nil

  /** the type name of the current frame */
  var frame_type_name: String = ""

  /** the type of the current frame (a tuple) */
  var frame_type: IRtype = VoidIRtype()

  /** LLVM needs a jump instruction before any label */
  var after_jump: Boolean = false

  /** representation of an LLVM temporary variable */
  case class Operand ( name: String)  {
    override def toString: String = name
  }

  var register_count = 1

  def new_temp_var (): Operand = {
    register_count += 1
    Operand("%R" + register_count)
  }

  var name_counter = 0

  /** generate a new  label name */
  def new_label (): String = {
    name_counter += 1
    "L_" + name_counter
  }

  /** emit an LLVM label */
  def llvm_label ( s: String ) {
    if (!after_jump)
      llvms(s"br label %$s")
    out.println(s"  $s:")
  }

  /** emit LLVM code */
  def llvms ( op: String ) {
    out.println(s"    $op")
  }

  /** emit LLVM code and bind the result to a new temp variable */
  def llvm ( op: String ): Operand = {
    val s = new_temp_var()
    out.println(s"    $s = $op")
    s
  }

  /** allocate a new string constant */
  def allocate_string ( s: String ): String =
    if (globals.contains(s))
      "S_"+globals.indexOf(s)
    else {
      globals = globals :+ s
      "S_"+(globals.length-1)
    }

  /** convert the type of an IRexp to an LLVM type */
  def llvm_type ( e: IRexp ): String
    = ltype(typeof(e))

  /** convert an IRtype to an LLVM type */
  def ltype ( tp: IRtype ): String =
    tp match {
      case BooleanIRtype()
        => "i1"
      case ByteIRtype()
        => "i8"
      case IntIRtype()
        => "i32"
      case FloatIRtype()
        => "float"
      case VoidIRtype()
        => "i8*"
      case StringIRtype()
        => "{i32,i8*}*"
      case NamedIRtype(nm,_)
        => s"%$nm"
      case AddressIRtype(etp)
        => ltype(etp) + "*"
      case VecIRtype(etp)
        => s"[0 x ${ltype(etp)}]"
      case TupleIRtype(cs)
        => cs.map(ltype).mkString("{ ", ", ", " }")
      case FunctionIRtype(as,VoidIRtype())
        => s"void ${as.map(ltype).mkString("( ", ", ", " )")}"
      case FunctionIRtype(as,ot)
        => s"${ltype(ot)} ${as.map(ltype).mkString("( ", ", ", " )")}"
      // a type variable in a polymorphic function must be able to coerce to i8*
      case TypeVarIRtype(_)
        => "i8*"
      case _ => throw new Error("Wrong IRtype: "+tp)
    }

  /* substitute type s for all occurences of the type variable v in the term t */
  def subst ( tv: String, s: IRtype, t: IRtype ): IRtype
    = t match {
        case TypeVarIRtype(v)
          => if (v == tv) s else t
        case AddressIRtype(a)
          => AddressIRtype(subst(tv,s,a))
        case NamedIRtype(n,ts)
          => NamedIRtype(n,ts.map(subst(tv,s,_)))
        case VecIRtype(et)
          => VecIRtype(subst(tv,s,et))
        case RecordIRtype(ts)
          => RecordIRtype(ts.map { case Bind(v,t) => Bind(v,subst(tv,s,t)) })
        case TupleIRtype(ts)
          => TupleIRtype(ts.map(subst(tv,s,_)))
        case FunctionIRtype(fps,ot)
          => FunctionIRtype(fps.map(subst(tv,s,_)),subst(tv,s,ot))
        case _ => t
      }

  /** expand the named types in an IRtype */
  def expand_type ( tp: IRtype ): IRtype =
    tp match {
      case NamedIRtype(name,ts)
        => expand_type(declarations.flatMap {
              case Bind(nm,IRtypeDecl(lnm,tvs,etp))
                if nm == name || lnm == name
                => List((tvs zip ts).foldLeft(etp) {
                              case (r,(v,t)) => subst(v,t,r)
                            })
              case _ => Nil
           }.head)
      case _ => tp
    }

  /** return the type of an IRexp */
  def typeof ( e: IRexp ): IRtype =
    e match {
      case IntValue(_)
        => IntIRtype()
      case FloatValue(_)
        => FloatIRtype()
      case BooleanValue(_)
        => BooleanIRtype()
      case StringValue(_)
        => StringIRtype()
      case NullValue()
        => VoidIRtype()
      case VoidValue()
        => VoidIRtype()
      case FramePointer()
        => AddressIRtype(NamedIRtype(frame_type_name,Nil))
      case Allocate(tp,_)
        => AddressIRtype(tp)
      case Closure(f,_)
        => declarations.flatMap {
              case Bind(_,IRfuncDecl(nm,_,_,fs,ot,_,_))
                if nm==f
                => val ftp = FunctionIRtype(AddressIRtype(ByteIRtype())::fs,ot)
                   List(AddressIRtype(TupleIRtype(List(AddressIRtype(ftp),
                                                       AddressIRtype(ByteIRtype())))))
              case _ => Nil
           }.head
      case Mem(a)
        => typeof(a) match {
              case AddressIRtype(tp)
                => tp
              case _ => throw new Error("Mem operation can only retrieve data from memory addresses: "+a)
           }
      case Indexed(l,r)
        => val ltp = typeof(l)
           val rtp = typeof(r)
           if (rtp != IntIRtype())
             throw new Error("Wrong pointer arithmetic: "+e)
           ltp match {
              case AddressIRtype(tp)
                => (expand_type(tp),r) match {
                      case (TupleIRtype(cs),IntValue(i))
                        => AddressIRtype(cs(i))
                      case (VecIRtype(etp),_)
                        => AddressIRtype(etp)
                      case (tp,_) => throw new Error("Wrong pointer arithmetic: "+e+" "+tp)
                   }
              case tp => throw new Error("Wrong pointer arithmetic: "+e+" "+tp)
           }
      case Binop(op,l,r)
        => val ltp = typeof(l)
           val rtp = typeof(r)
           if (ltp != rtp)
             throw new Error("Incompatible types in binary operation: "+e+" "+ltp+" <> "+rtp)
           else if (op.equals("AND") || op.equals("OR"))
                  if (ltp == BooleanIRtype())
                    ltp
                  else throw new Error("AND/OR operation can only be applied to booleans: "+e)
                else if (op.equals("EQ") || op.equals("NEQ"))
                       BooleanIRtype()
                else if (ltp != IntIRtype() && ltp != FloatIRtype())
                       throw new Error("Binary arithmetic operations can only be applied to integers or floats: "+e)
                else if (op.equals("GT") || op.equals("LT") || op.equals("GEQ") || op.equals("LEQ"))
                       BooleanIRtype()
                else ltp
      case Unop(op,u)
        => val tp = typeof(u)
           if (op.equals("NOT"))
              if (tp == BooleanIRtype())
                tp
              else throw new Error("NOT can only be applied to booleans: "+e)
           else if (tp != IntIRtype() && tp != FloatIRtype())
              throw new Error("Unary +/- can only be applied to integer or real numbers"+e)
           else tp
      case Address(name)
        => declarations.flatMap {
              case Bind(_,IRfuncDecl(nm,_,_,fs,ot,_,_))
                if nm==name
                => List(AddressIRtype(FunctionIRtype(AddressIRtype(ByteIRtype())::fs,ot)))
              case _ => Nil
           }.head
      case Call(f, _, _)
        => typeof(f) match {
              case AddressIRtype(FunctionIRtype(_,otp))
                => otp
              case AddressIRtype(TupleIRtype(List(AddressIRtype(FunctionIRtype(_,otp)),_)))
                => otp
              case tp => throw new Error("Not a function: "+f+" of type "+tp)
            }
      case TypeSize(_)
        => IntIRtype()
      case Coerce(_,_,tp)
        => tp
      case _ => throw new Error("Wrong IRexp: "+e)
    }

  /** generate LLVM code from the IR expression e and return the
    * temporary variable that will hold the result */
  def emit ( e: IRexp ): Operand =
    e match {
      case IntValue(n)
        => Operand(n.toString)
      case FloatValue(n)
        => Operand("0x"+java.lang.Double.doubleToLongBits(n.toDouble).toHexString)
      case BooleanValue(b)
        => Operand(if (b) "1" else "0")
      case StringValue(s)
        => val len = s.length + 1
           Operand("@"+allocate_string(s))
      case NullValue()
        => Operand("null")
      case VoidValue()
        => Operand("null")
      case Address(a)
        => Operand("@"+a)
      case Closure(f,s)
        => typeof(e) match {
             case AddressIRtype(tp@TupleIRtype(List(g@AddressIRtype(FunctionIRtype(_::fs,ot)),_)))
               => val ltp = ltype(tp)
                  val gtp = ltype(g)
                  val sltp = typeof(s)
                  val ftp = ltype(FunctionIRtype(sltp::fs,ot))
                  val sz = llvm(s"zext i32 ${emit(TypeSize(tp))} to i64")
                  val c = llvm(s"call noalias i8* @GC_malloc(i64 $sz)")
                  val closure = llvm(s"bitcast i8* $c to $ltp*")
                  val c0 = llvm(s"getelementptr $ltp, $ltp* $closure, i32 0, i32 0")
                  val ff = llvm(s"bitcast $ftp* @$f to $gtp")
                  llvms(s"store $gtp $ff, $gtp* $c0")
                  val c1 = llvm(s"getelementptr $ltp, $ltp* $closure, i32 0, i32 1")
                  val sl = llvm(s"bitcast ${ltype(sltp)} ${emit(s)} to i8*")
                  llvms(s"store i8* $sl, i8** $c1")
                  closure
             }
      case FramePointer()
        => Operand("%fp")
      case Mem(a)
        => typeof(a) match {
              case AddressIRtype(tp)
                => val ltp = ltype(tp)
                   llvm(s"load $ltp, $ltp* ${emit(a)}")
              case _ => throw new Error("Wrong address: "+a)
           }
      case Indexed(a, i)
        => typeof(a) match {
              case AddressIRtype(tp)
                => val ltp = ltype(tp)
                   llvm(s"getelementptr $ltp, $ltp* ${emit(a)}, i32 0, i32 ${emit(i)}")
              case tp => throw new Error("Wrong pointer arithmetic on type "+tp+" in "+e)
            }
      case Binop(op, x, y)
        => val tp = llvm_type(x)
           val llvm_op = if (tp == "i32")
             op match {
            case "PLUS" => "add"
            case "TIMES" => "mul"
            case "MINUS" => "sub"
            case "DIV" => "div"
            case "MOD" => "srem"
            case "EQ" => "icmp eq"
            case "NEQ" => "icmp ne"
            case "GT" => "icmp sgt"
            case "GEQ" => "icmp sge"
            case "LT" => "icmp slt"
            case "LEQ" => "icmp sle"
            case _ => throw new Error("*** Wrong binary int operation "+e)
          }
        else if (tp == "float")
          op match {
            case "PLUS" => "fadd"
            case "TIMES" => "fmul"
            case "MINUS" => "fsub"
            case "DIV" => "fdiv"
            case "EQ" => "icmp eq"
            case "NEQ" => "icmp ne"
            case "GT" => "fcmp sgt"
            case "GEQ" => "fcmp sge"
            case "LT" => "fcmp slt"
            case "LEQ" => "fcmp sle"
            case _ => throw new Error("*** Wrong binary float operation "+e)
          }
        else if (tp == "i1")
          op match {
            case "EQ" => "icmp eq"
            case "NEQ" => "icmp ne"
            case "AND" => "and"
            case "OR" => "or"
            case _ => throw new Error("*** Wrong boolean operation "+e)
          }
        else op match {
            case "EQ" => "icmp eq"
            case "NEQ" => "icmp ne"
            case _ => throw new Error("*** Wrong binary operation "+e+" on type "+tp)
        }
        llvm(s"$llvm_op $tp ${emit(x)}, ${emit(y)}")
      case Unop("NOT", x)
        => llvm(s"xor i1 ${emit(x)}, 1")
      case Unop("MINUS", x)
        => val tp = llvm_type(x)
           if (tp == "i32")
             llvm(s"sub i32 0, ${emit(x)}")
           else llvm(s"fsub float 0.0, ${emit(x)}")
      case Call(Address(f), sl, args)    // f is a defined function
        => val tp = llvm_type(e)
           val as = ((llvm_type(sl)+" "+emit(sl))::args.map(a => llvm_type(a) + " " + emit(a))).mkString(", ")
           llvm(s"call $tp @$f ( $as )")
      case Call(f, _, args)              // f is the closure of an anonymous function
        => typeof(f) match {
             case AddressIRtype(ctp@TupleIRtype(List(lf@AddressIRtype(FunctionIRtype(_,otp)),frame)))
               => val closure = emit(f)
                  val lctp = ltype(ctp)
                  val fa = llvm(s"getelementptr $lctp, $lctp* $closure, i32 0, i32 0")
                  val ff = llvm(s"load ${ltype(lf)}, ${ltype(lf)}* $fa   ; get the function address from closure")
                  val sl = llvm(s"getelementptr $lctp, $lctp* $closure, i32 0, i32 1")
                  val ss = llvm(s"load ${ltype(frame)}, ${ltype(frame)}* $sl   ; get the static link from closure")
                  val as = ((ltype(frame)+" "+ss)::args.map(a => llvm_type(a) + " " + emit(a))).mkString(", ")
                  llvm(s"call ${ltype(otp)} $ff ( $as )")
              case _ => throw new Error("Expected a closure: "+f)
           }
      case Allocate(tp,size)
        => val sz = llvm(s"zext i32 ${emit(size)} to i64")
           val p = llvm(s"call noalias i8* @GC_malloc(i64 $sz)")
           llvm(s"bitcast i8* $p to ${ltype(tp)}*")
      case TypeSize(tp)
        => ltype(tp) match {
             case "i8" => Operand("1")
             case "i32" => Operand("4")
             case "i64" => Operand("8")
             case "float" => Operand("4")
             case ltp
               => val size = llvm(s"getelementptr $ltp, $ltp* null, i32 1 ; calculate the size in bytes")
                  llvm(s"ptrtoint $ltp* $size to i32")
           }
      case ESeq(s,u)
        => emit(s,IntIRtype())
           emit(u)
      case Coerce(u,from,to)
        => val ft = ltype(from)
           val tt = ltype(to)
           val cu = emit(u)
           if (from == to)
             cu
           else if (from.isInstanceOf[TypeVarIRtype])
             to match {
                case IntIRtype() | BooleanIRtype() | ByteIRtype()
                  => llvm(s"ptrtoint $ft $cu to $tt")
                case FloatIRtype()
                  => val ci = llvm(s"ptrtoint $ft $cu to i32")
                     llvm(s"bitcast i32 $ci to $tt")
                case _ => llvm(s"bitcast $ft $cu to $tt")
             }
           else if (to.isInstanceOf[TypeVarIRtype])
             from match {
                case IntIRtype() | BooleanIRtype() | ByteIRtype()
                  => llvm(s"inttoptr $ft $cu to $tt")
                case FloatIRtype()
                  => val ci = llvm(s"bitcast $ft $cu to i32")
                     llvm(s"inttoptr i32 $ci to $tt")
                case _ => llvm(s"bitcast $ft $cu to $tt")
             }
           else llvm(s"bitcast $ft $cu to $tt")
      case _ => throw new Error("Wrong IRexp: "+e)
    }

  /** generate LLVM code from an IR statement */
  def emit ( e: IRstmt, return_type: IRtype ) {
    out.println(Pretty.print(e.toString,"; "))
    after_jump = false
    e match {
      case Move(Mem(d),s)
        => val dtp = typeof(Mem(d))
           val stp = typeof(s)
           val source = emit(Coerce(s,stp,dtp))
           llvms(s"store ${ltype(dtp)} $source, ${ltype(dtp)}* ${emit(d)}")
      case Label(n)
        => llvm_label(n)
      case Jump(n)
        => llvms(s"br label %$n")
           after_jump = true
      case CJump(c,n)
        => val next = new_label()
           llvms(s"br i1 ${emit(c)}, label %$n, label %$next")
           after_jump = true
           llvm_label(next)
      case CallP(Address(f), sl, args)
        => val as = ((llvm_type(sl)+" "+emit(sl))::args.map(a => llvm_type(a) + " " + emit(a))).mkString(", ")
           llvms(s"call void @$f ( $as )")
      case CallP(f, _, args)              // f is the closure of an anonymous function
        => typeof(f) match {
             case AddressIRtype(ctp@TupleIRtype(List(lf@AddressIRtype(FunctionIRtype(_,_)),frame)))
               => val closure = emit(f)
                  val lctp = ltype(ctp)
                  val fa = llvm(s"getelementptr $lctp, $lctp* $closure, i32 0, i32 0")
                  val ff = llvm(s"load ${ltype(lf)}, ${ltype(lf)}* $fa   ; get the function address from closure")
                  val sl = llvm(s"getelementptr $lctp, $lctp* $closure, i32 0, i32 1")
                  val ss = llvm(s"load ${ltype(frame)}, ${ltype(frame)}* $sl   ; get the static link from closure")
                  val as = ((ltype(frame)+" "+ss)::args.map(a => llvm_type(a) + " " + emit(a))).mkString(", ")
                  llvms(s"call void $ff ( $as )")
              case _ => throw new Error("Expected a closure: "+f)
           }
      case Assert(c)
        => val cont = new_label()
           val next = new_label()
           llvms(s"br i1 ${emit(c)}, label %$cont, label %$next")
           after_jump = true
           llvm_label(next)
           emit(SystemCall("WRITE_STRING",StringValue("Assertion error: "+c)),return_type)
           llvms("call void @exit ( i32 1 )")
           llvms("unreachable")
           llvm_label(cont)
      case Return(VoidValue())
        => llvms(s"ret void")
      case Return(v)
        => val etp = ltype(return_type)
           val vtp = llvm_type(v)
           val sv = if (etp != vtp)
                      llvm(s"bitcast $vtp ${emit(v)} to $etp")
                    else emit(v)
           llvms(s"ret $etp $sv")
      case Seq(s)
        => s.foreach(emit(_,return_type))
      case SystemCall("WRITE_INT",a)
        => val v = typeof(a) match {
                      case t@TypeVarIRtype(_)
                        => Coerce(a,t,IntIRtype())
                      case _ => a
                   }
           llvms(s"call i32 @puti ( i32 ${emit(v)} )")
      case SystemCall("WRITE_FLOAT",a)
        => val v = typeof(a) match {
                      case t@TypeVarIRtype(_)
                        => Coerce(a,t,FloatIRtype())
                      case _ => a
                   }
           llvms(s"call i32 @putf ( float ${emit(v)} )")
      case SystemCall("WRITE_STRING",StringValue("\\n"))
        => val nl = llvm("getelementptr inbounds [2 x i8], [2 x i8]* @.new_line, i32 0, i32 0")
           llvms(s"call i32(i8*, ...) @printf ( i8* $nl )")
      case SystemCall("WRITE_STRING",a)
        => val v = llvm(s"getelementptr inbounds {i32,i8*}, {i32,i8*}* ${emit(a)}, i32 0, i32 1")
           val w = llvm(s"load i8*, i8** $v")
           llvms(s"call i32(i8*, ...) @printf ( i8* $w )")
      case SystemCall("READ_INT",a)
        => llvms(s"call i32 @geti ( i32* ${emit(a)} )")
      case SystemCall("READ_FLOAT",a)
        => llvms(s"call i32 @getf ( float* ${emit(a)} )")
      case SystemCall("READ_STRING",a)
        => llvms(s"call i32 @getf ( i8* ${emit(a)} )")
      case _ => throw new Error("Wrong IRstmt: "+e)
    }
  }

  /** true, if the type tp contains a functional type */
  def contains_functional ( tp: IRtype ): Boolean =
    tp match {
      case FunctionIRtype(_,_)
        => true
      case VecIRtype(et)
        => contains_functional(et)
      case TupleIRtype(ts)
        => ts.map(contains_functional).reduce(_||_)
      case AddressIRtype(a)
        => contains_functional(a)
      case _ => false
  }

  /** emit LLVM code for a declaration */
  def emit ( e: IRdecl ) {
    e match {
      case IRfuncDecl("main",fl,_,_,_,_,body)
        => frame_type = TupleIRtype(fl)
           frame_type_name = "main_frame"
           register_count = 0
           out.println("define i32 @main ( i32, i8** ) {")
           llvms("%fp = alloca %main_frame")
           body.foreach(emit(_,VoidIRtype()))
           llvms("ret i32 0")
           out.println("}\n")
      case IRfuncDecl(fn,fl,_,fs,ot,_,body)
        => frame_type_name = fn+"_frame"
           frame_type = TupleIRtype(fl)
           register_count = 0
           val sl_type = ltype(fl.head)
           val args = (sl_type::fs.map(ltype)).mkString(", ")
           if (ot == VoidIRtype())
             out.println(s"define void @$fn ( $args ) {")
           else out.println(s"define ${ltype(ot)} @$fn ( $args ) {")
           if (!contains_functional(ot))
              llvms(s"%fp = alloca %$frame_type_name")
           else { // the frame for a function that returns a closure must be allocated in the heap
              val size = emit(TypeSize(frame_type))     // emit code to calculate frame size
              val sz = llvm(s"zext i32 $size to i64")
              val p = llvm(s"call noalias i8* @GC_malloc(i64 $sz)   ; allocate the frame in the heap")
              llvms(s"%fp = bitcast i8* $p to %$frame_type_name*")
           }
           val sl = llvm(s"getelementptr %$frame_type_name, %$frame_type_name* %fp, i32 0, i32 0")
           llvms(s"store $sl_type %0, $sl_type* $sl")
           fs.zipWithIndex.foreach {
              case (x,i)
                => val tp = ltype(x)
                   val a = llvm(s"getelementptr %$frame_type_name, %$frame_type_name* %fp, i32 0, i32 ${i+1}")
                   llvms(s"store $tp %${i+1}, $tp* $a   ; store the ${i+1}'th argument in the frame")
              }
           body.foreach(emit(_,ot))
           ot match {
             case VoidIRtype()
               => llvms("ret void")
             case _ => llvms("unreachable")
           }
           out.println("}\n")
      case IRtypeDecl(nm,_,tp)
        => val ltp = ltype(expand_type(tp))
           out.println(s"%$nm = type $ltp\n")
      case _ => ;
    }
  }

  /** emit LLVM code for the program */
  def emit ( program: List[Bind[IRdecl]] ): Unit = {
    frame_type_name = "main_frame"
    declarations = program
    program.foreach { case Bind(_,d:IRtypeDecl) => emit(d); case _ => ; }
    program.foreach { case Bind(_,d:IRfuncDecl) => emit(d); case _ => ; }
    out.print("""declare noalias i8* @GC_malloc ( i64 )
declare i32 @printf ( i8*, ... )
declare i32 @scanf ( i8*, ... )
declare void @exit ( i32 )
@.sfi = private unnamed_addr constant [3 x i8] c"%i\00", align 1
@.sff = private unnamed_addr constant [3 x i8] c"%f\00", align 1
@.sfs = private unnamed_addr constant [3 x i8] c"%s\00", align 1
define i32 @puti ( i32 ) {
  %f = getelementptr inbounds [3 x i8], [3 x i8]* @.sfi, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %f, i32 %0)
  ret i32 0
}
define i32 @geti ( i32* ) {
  %f = getelementptr inbounds [3 x i8], [3 x i8]* @.sfi, i32 0, i32 0
  call i32 (i8*, ...) @scanf(i8* %f, i32* %0)
  ret i32 0
}
define i32 @putf ( float ) {
  %f = getelementptr inbounds [3 x i8], [3 x i8]* @.sff, i32 0, i32 0
  %d = fpext float %0 to double
  call i32 (i8*, ...) @printf(i8* %f, double %d)
  ret i32 0
}
define i32 @getf ( float* ) {
  %f = getelementptr inbounds [3 x i8], [3 x i8]* @.sff, i32 0, i32 0
  call i32 (i8*, ...) @scanf(i8* %f, float* %0)
  ret i32 0
}
define i32 @gets ( i8* ) {
  %f = getelementptr inbounds [3 x i8], [3 x i8]* @.sfs, i32 0, i32 0
  call i32 (i8*, ...) @scanf(i8* %f, i8* %0)
  ret i32 0
}
@.new_line = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
""")
    val quote = "\""
    globals.zipWithIndex.foreach {
      case (s,i)
        => val len = s.length+1
           out.println(s"@S_c_$i = private unnamed_addr constant [$len x i8] c$quote$s\\00$quote, align 1")
           out.println(s"@S_$i = private unnamed_addr constant {i32,i8*} { i32 $len, i8* bitcast([$len x i8]* @S_c_$i to i8*) }")
    }
  }
}
