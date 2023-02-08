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

object TypeInference {
  import AST._

  var trace_type_inference = false

  /** symbol table to store SSC declarations */
  var st = new SymbolTable[Declaration]

  type Env = Either[ String,                // fail with a message
                     List[(String,Type)] ]  // subst list

  var env: Env = Right(Nil)

  def error ( msg: String ): Type = {
    System.err.println("*** Type Inference Error: "+msg)
    System.err.println("*** Symbol Table: "+st)
    System.exit(1)
    null
  }

  /* Tracing level */
  var trace_level: Int = -1

  def typevars ( tp: Type ): List[String]
    = tp match {
        case TypeParameter(v) => List(v)
        case _ => accumulate[List[String]](tp,typevars,_++_,Nil)
      }

  /* check if the type variable tv occurs in the term t */
  def occurs ( tv: String, t: Type ): Boolean
    = t match {
        case TypeParameter(v)
          => tv == v
        case _ => accumulate[Boolean](t,occurs(tv,_),_||_,false)
      }

  /* substitute type s for all occurences of the type variable v in the term t */
  def subst ( tv: String, s: Type, t: Type ): Type
    = t match {
        case TypeParameter(v)
          => if (v == tv) s else t
        case _ => AST.apply(t,subst(tv,s,_))
      }

  def subst ( typeParams: List[String], types: List[Type], tp: Type ): Type
    = (typeParams zip types).foldLeft[Type](tp) {
                                case (r,(v,tp)) => subst(v,tp,r)
                             }

  def apply ( env: Env, t: Type ): Type
    = env match {
        case Right(es) => es.foldRight(t) { case ((v,tp),r) => subst(v,tp,r) }
        case Left(msg) => error(msg)
      }

  var fresh_var_count: Int = 0

  def fresh_var (): String = {
    fresh_var_count += 1
    "_tp_"+fresh_var_count
  }

  def fresh ( typeParams: List[String], tp: Type ): (List[String],Type) = {
    val fvs = typeParams.map(x => fresh_var())
    (fvs, (typeParams zip fvs).foldLeft[Type](tp) {
                              case (r,(v,fv)) => subst(v,TypeParameter(fv),r)
                         })
  }

  def trace ( t1: Type, t2: Type, result: => Env ): Env = {
    if (trace_type_inference) {
       trace_level += 1
       println(".  "*trace_level+"$$ unify "+t1)
       println(".  "*trace_level+".   with "+t2)
    }
    val res = result
    if (trace_type_inference) {
       println(".  "*trace_level+"-> "+(res match { case Right(_) => "success"; case _ => "fail" }))
       trace_level -= 1
    }
    res
  }

  def unify_lists ( ts1: List[Type], ts2: List[Type] ): Env
    = if (ts1.length != ts2.length)
        Left(s"incompatible types: $ts1 $ts2")
      else (ts1 zip ts2).foldLeft[Env](Right(Nil)) {
              case (e@Right(s),(t1,t2))
                => unify(apply(e,t1),apply(e,t2)) match {
                     case Right(r) => Right(r++s)
                     case f => f
                   }
              case (f,_) => f
           }

  def unify ( t1: Type, t2: Type ): Env
    = trace(t1,t2,(t1,t2) match {
         case _
           if (t1 == t2 || t1.isInstanceOf[AnyType] || t2.isInstanceOf[AnyType])
           => Right(Nil)
         case (TypeParameter(v1),TypeParameter(v2))
           => Right(if (v1 == v2) Nil else List((v1,t2)))
         case (TypeParameter(v),t)
           => if (occurs(v,t))
                Left(s"not unifiable due to circularity: $t1 $t2")
              else Right(List((v,t)))
         case (t,TypeParameter(v))
           => if (occurs(v,t))
                Left(s"not unifiable due to circularity: $t1 $t2")
              else Right(List((v,t)))
         case (ArrayType(te1),ArrayType(te2))
           => unify(te1,te2)
         case (TupleType(ts1),TupleType(ts2))
           => unify_lists(ts1,ts2)
         case (RecordType(bs1),RecordType(bs2))
           => if (bs1.map(_.name) != bs2.map(_.name))
                Left(s"incompatible component names in records: $t1 $t2")
              else unify_lists(bs1.map(_.value),bs2.map(_.value))
         case (FunctionType(ts1,to1),FunctionType(ts2,to2))
           => unify_lists(ts1,ts2) match {
                case e@Right(s)
                  => unify(apply(e,to1),apply(e,to2)) match {
                       case Right(r) => Right(s++r)
                       case f => f
                     }
                case f => f
              }
         case (NamedType(nm1,ts1),NamedType(nm2,ts2))
           if nm1 == nm2
           => unify_lists(ts1,ts2)
         case (NamedType(nm,ts),_)
           => st.lookup(nm) match {
                 case Some(TypeDeclaration(vts,tt))
                   => val (vs,t) = fresh(vts,tt)
                      if (vs.length == ts.length)
                        unify(subst(vs,ts,t),t2)
                      else Left(s"wrong number of type arguments in $t2")
                 case _ => Left("Undeclared type: "+t1)
              }
         case (_,NamedType(nm,ts))
           => st.lookup(nm) match {
                 case Some(TypeDeclaration(vts,tt))
                   => val (vs,t) = fresh(vts,tt)
                      if (vs.length == ts.length)
                        unify(t1,subst(vs,ts,t))
                      else Left(s"wrong number of type arguments in $t2")
                 case _ => Left("Undeclared type: "+t2)
              }
         case _
           => Left(s"incompatible types: $t1 $t2")
      })

  /** If tp is a named type, expand it */
  def expandType ( tp: Type, polymorphic: Boolean = false ): Type
    = tp match {
         case NamedType(nm,ts)
           => st.lookup(nm) match {
                 case Some(TypeDeclaration(vts,tt))
                   => val (vs,t) = fresh(vts,tt)
                      expandType(if (polymorphic) t else subst(vs,ts,t))
                 case _ => error("Undeclared type: "+tp)
              }
         case _ => tp
      }

  def typeEquivalence ( tp1: Type, tp2: Type ): Boolean
    = unify(tp1,tp2).isRight

  def trace[T] ( e: Any, result: => T ): T = {
    if (trace_type_inference) {
       trace_level += 1
       println(".  "*trace_level+"** "+e)
    }
    val res = result
    if (trace_type_inference) {
       print(".  "*trace_level)
       if (e.isInstanceOf[Stmt] || e.isInstanceOf[Definition])
          println("->")
       else println("-> "+res)
       trace_level -= 1
    }
    res
  }

  /** type_inference an expression AST */
  def type_inference ( e: Expr ): Type
    = if (e.tpe != null)
        e.tpe   // the cached type of e
      else { val tpe = trace(e,e match {
      case IntConst(_) => IntType()
      case FloatConst(_) => FloatType()
      case StringConst(_) => StringType()
      case BooleanConst(_) => BooleanType()
      case NullExp() => AnyType()
      case BinOpExp(op,l,r)
        => val ltp = type_inference(l)
           val rtp = type_inference(r)
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
      case UnOpExp(op,u)
        => val tp = type_inference(u)
           if (op.equals("not"))
              if (typeEquivalence(tp,BooleanType()))
                 tp
              else error("NOT can only be applied to booleans: "+e)
           else if (!typeEquivalence(tp,IntType()) && !typeEquivalence(tp,FloatType()))
                   error("Unary +/- can only be applied to integer or real numbers"+e)
           else tp
      case Var(name)
        => st.lookup(name) match {
              case Some(VarDeclaration(t,_,_)) => t
              case Some(FuncDeclaration(vs,ot,fs,_,_,_))
                => fresh(vs,FunctionType(fs.map(_.value),ot))._2
              case Some(_) => error(name+" is not a variable")
              case None => error("Undefined variable: "+name)
        }
      case ArrayDeref(array,index)
        => if (!typeEquivalence(type_inference(index),IntType()))
             error("Array index must be integer: "+e)
           expandType(type_inference(array)) match {
              case ArrayType(tp) => tp
              case _ => error("Array indexing can only be done on arrays: "+e)
           }
      case RecordDeref(rec,attr)
        => expandType(type_inference(rec)) match {
             case RecordType(cs)
                => cs.find{ case Bind(c,_) => c == attr } match {
                     case Some(Bind(_,tp)) => tp
                     case _ => error("Record does not have the component: "+attr)
                   }
             case ArrayType(_) if attr == "length"
                => IntType()
             case _ => error("Record projection can only be done on records: "+e)
           }
      case TupleDeref(t,i)
        => expandType(type_inference(t)) match {
             case TupleType(cs)
                => if (i >= cs.length)
                      error("Tuple does not have "+i+" elements")
                   cs(i)
             case _ => error("Tuple projection can only be done on tuples: "+e)
           }
      case CallExp(f,args)
        => st.lookup(f) match {
              case Some(FuncDeclaration(vs,ot,ps,_,_,_))
                 => val FunctionType(params,otp) = fresh(vs,FunctionType(ps.map(_.value),ot))._2
                    if (params.length != args.length)
                      error("Number of formal parameters does not match the number of arguments in call: "+e)
                    else apply(unify_lists(params,args.map(type_inference)),otp)
              case Some(VarDeclaration(FunctionType(params,otp),_,_))
                 => if (params.length != args.length)
                      error("Number of formal parameters does not match the number of arguments in call: "+e)
                    else apply(unify_lists(params,args.map(type_inference)),otp)
              case Some(_) => error("Not a function: "+f)
              case _ => error("Undefined function: "+f)
          }
      case RecordExp(cs)
        => RecordType(cs.map{ case Bind(c,v) => Bind(c,type_inference(v)) })
      case TupleExp(cs)
        => TupleType(cs.map(type_inference))
      case ArrayGen(len,v)
        => if (!typeEquivalence(type_inference(len),IntType()))
             error("The array length must be integer: "+e)
           ArrayType(type_inference(v))
      case ArrayExp(cs)
        => val tp::ts = cs.map(type_inference)
           ts.zip(cs.tail).foreach {
             case (t,u)
               => if (!typeEquivalence(t,tp))
                     error("The type of "+u+" in the array is "+t
                           +", but it was expected to be "+tp)
           }
           ArrayType(tp)
      case FunctionExp(fs,ot,b)
        => st.begin_scope()
           fs.foreach{ case Bind(v,tp) => st.insert(v,VarDeclaration(tp,0,0)) }
           type_inference(b,ot)
           st.end_scope()
           FunctionType(fs.map(_.value),ot)
    } )
    e.tpe = tpe
    tpe
  }

  /** type_inference a statement AST using the expected type of the return value from the current function */
  def type_inference ( e: Stmt, expected_type: Type ) {
    trace(e,e match {
      case AssignSt(RecordDeref(rec,"length"),_)
        if expandType(type_inference(rec)).isInstanceOf[ArrayType]
        => error("You cannot change the length of an array: "+e)
      case AssignSt(d,s)
        => if (!typeEquivalence(type_inference(d),type_inference(s)))
             error("Incompatible types in assignment: "+e)
      case CallSt(f,args)
        => st.lookup(f) match {
          case Some(FuncDeclaration(vs,ot@NoType(),ps,_,_,_))
            => val FunctionType(params,otp) = fresh(vs,FunctionType(ps.map(_.value),ot))._2
               if (params.length != args.length)
                 error("Number of formal parameters does not match the number of arguments in call: "+e)
               else apply(unify_lists(params,args.map(type_inference)),otp)
          case Some(VarDeclaration(FunctionType(params,otp@NoType()),_,_))
            => if (params.length != args.length)
                 error("Number of formal parameters does not match the number of arguments in call: "+e)
               else apply(unify_lists(params,args.map(type_inference)),otp)
          case Some(_) => error("Not a procedure: "+f)
          case _ => error("Undefined procedure: "+f)
        }
      case ReadSt(args)
        => for ( arg <- args ) {
              val t = type_inference(arg)
              if (!typeEquivalence(t,BooleanType())
                  && !typeEquivalence(t,IntType())
                  && !typeEquivalence(t,FloatType())
                  && !typeEquivalence(t,StringType()))
                 error("Expected primitive type in READ statement: "+e)
          }
      case PrintSt(args)
        => for ( arg <- args ) {
              val t = type_inference(arg)
              if (!typeEquivalence(t,BooleanType())
                  && !typeEquivalence(t,IntType())
                  && !typeEquivalence(t,FloatType())
                  && !typeEquivalence(t,StringType()))
                 error("Expected primitive type in WRITE statement: "+e)
          }
      case IfSt(p,a,b)
        => if (!typeEquivalence(type_inference(p),BooleanType()))
              error("Expected a boolean in IF test: "+p)
           type_inference(a,expected_type)
           if (b != null)
              type_inference(b,expected_type)
      case WhileSt(p,s)
        => if (!typeEquivalence(type_inference(p),BooleanType()))
              error("Expected a boolean in WHILE test: "+p)
           type_inference(s,expected_type)
      case LoopSt(s)
        => type_inference(s,expected_type)
      case ForSt(v,a,b,c,s)
        => if (!typeEquivalence(type_inference(a),IntType()))
              error("initial value in FOR loop must be integer: "+a)
           if (!typeEquivalence(type_inference(b),IntType()))
              error("step in FOR loop must be integer: "+b)
           if (!typeEquivalence(type_inference(c),IntType()))
              error("final value in FOR loop must be integer: "+c)
           st.begin_scope()
           st.insert(v,VarDeclaration(IntType(),0,0))
           type_inference(s,expected_type)
           st.end_scope()
      case ExitSt() => ;
      case ReturnSt()
        => if (!typeEquivalence(expected_type,NoType()))
              error("Expected a returned value of a non-void type: "+e)
      case ReturnValueSt(u)
        => if (expected_type == NoType())
              error("Cannot return a value from a procedure: "+e)
           val tp = type_inference(u)
           if (!typeEquivalence(expected_type,tp))
              error("Expected a returned value of a different type: "+e)
      case BlockSt(dl)
        => st.begin_scope()
           dl.foreach {
             case Left(d) => type_inference(d)
             case Right(s) => type_inference(s,expected_type)
           }
           st.end_scope()
    } )
  }

  def check_type ( tp: Type ): Type
    = tp match {
        case NamedType(nm,ts)
          => st.lookup(nm) match {
                case Some(TypeDeclaration(vs,t))
                  => if (vs.length != ts.length)
                       error("Wrong number of type arguments: "+tp)
                     NamedType(nm,ts.map(check_type))
                case _ => error("Undeclared type: "+tp)
             }
        case _ => AST.apply(tp,check_type)
      }

  /** type_inference a definition */
  def type_inference ( e: Definition ) {
    trace(e,e match {
      case TypeDef(vs,n,tp)
        => if (vs.distinct.length != vs.length)
             error("Duplicate type parameters: "+e)
           st.insert(n,TypeDeclaration(vs,tp))
           check_type(tp)
      case VarDef(v,tp,u)
        => if (tp == AnyType())
              st.insert(v,VarDeclaration(type_inference(u),0,0))
           else if (u != null && !typeEquivalence(type_inference(u),tp))
                   error("Incompatible types in variable declaration: "+e)
           else st.insert(v,VarDeclaration(tp,0,0))
           check_type(tp)
      case FuncDef(vs,f,ps,ot,b)
        => if (vs.distinct.length != vs.length)
             error("Duplicate type parameters: "+e)
           st.insert(f,FuncDeclaration(vs,ot,ps,"",0,0))
           st.begin_scope()
           ps.foreach { case Bind(v,tp)
                          => st.insert(v,VarDeclaration(tp,0,0))
                             check_type(ot)
                      }
           check_type(ot)
           type_inference(b,ot)
           st.end_scope()
    } )
  }

  /** type_inference the main program */
  def type_inference ( e: Program ) {
    type_inference(e.body,NoType())
  }
}
