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

object TypeChecker {

  var trace_typecheck = false

  /** symbol table to store SSC declarations */
  var st = new SymbolTable[Declaration]

  def error ( msg: String ): Type = {
    System.err.println("*** Typechecking Error: "+msg)
    System.err.println("*** Symbol Table: "+st)
    System.exit(1)
    null
  }

  /** If tp is a named type, expand it */
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
             case NamedType(_)
               => typeEquivalence(tp1,expandType(tp2))
             case _ => false
           }
    }

  /* Tracing level */
  var level: Int = -1

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
      case IntConst(_) => IntType()
      case FloatConst(_) => FloatType()
      case StringConst(_) => StringType()
      case BooleanConst(_) => BooleanType()
      case NullExp() => AnyType()
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
      case UnOpExp(op,u)
        => val tp = typecheck(u)
           if (op.equals("not"))
              if (typeEquivalence(tp,BooleanType()))
                 tp
              else error("NOT can only be applied to booleans: "+e)
           else if (!typeEquivalence(tp,IntType()) && !typeEquivalence(tp,FloatType()))
                   error("Unary +/- can only be applied to integer or real numbers"+e)
           else tp
      case LvalExp(lv)
        => typecheck(lv)
      case CallExp(f,args)
        => st.lookup(f) match {
              case Some(FuncDeclaration(otp,params,_,_,_))
                 => if (params.length != args.length)
                      error("Number of formal parameters does not much the number of arguments in call: "+e)
                    else (args.map(typecheck) zip params).map {
                             case (atp,Bind(_,ptp))
                               => if (!typeEquivalence(atp,ptp))
                                     error("The type of call argument ("+atp
                                           +") does not match the type of the formal parameter: "+ptp)
                         }
                    otp
              case Some(VarDeclaration(FunctionType(params,otp),_,_))
                 => if (params.length != args.length)
                      error("Number of formal parameters does not much the number of arguments in call: "+e)
                    else (args.map(typecheck) zip params).map{
                             case (atp,ptp)
                               => if (!typeEquivalence(atp,ptp))
                                    error("The type of call argument ("+atp
                                          +") does not match the type of the formal parameter: "+ptp)
                         }
                    otp
              case Some(_) => error("Not a function: "+f)
              case _ => error("Undefined function: "+f)
          }
      case RecordExp(cs)
        => RecordType(cs.map{ case Bind(c,v) => Bind(c,typecheck(v)) })
      case TupleExp(cs)
        => TupleType(cs.map(typecheck))
      case ArrayGen(len,v)
        => if (!typeEquivalence(typecheck(len),IntType()))
             error("The array length must be integer: "+e)
           ArrayType(typecheck(v))
      case ArrayExp(cs)
        => val tp::ts = cs.map(typecheck)
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
           typecheck(b,ot)
           st.end_scope()
           FunctionType(fs.map(_.value),ot)
    } )

  /** typecheck an Lvalue AST */
  def typecheck ( e: Lvalue ): Type =
    trace(e,e match {
      case Var(name)
        => st.lookup(name) match {
              case Some(VarDeclaration(t,_,_)) => t
              case Some(FuncDeclaration(ot,fs,_,_,_))
                => FunctionType(fs.map(_.value),ot)
              case Some(_) => error(name+" is not a variable")
              case None => error("Undefined variable: "+name)
        }
      case ArrayDeref(array,index)
        => if (!typeEquivalence(typecheck(index),IntType()))
             error("Array index must be integer: "+e)
           expandType(typecheck(array)) match {
              case ArrayType(tp) => tp
              case _ => error("Array indexing can only be done on arrays: "+e)
           }
      case RecordDeref(rec,attr)
        => expandType(typecheck(rec)) match {
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
        => expandType(typecheck(t)) match {
             case TupleType(cs)
                => if (i >= cs.length)
                      error("Tuple does not have "+i+" elements")
                   cs(i)
             case _ => error("Tuple projection can only be done on tuples: "+e)
           }
    } )

  /** typecheck a statement AST using the expected type of the return value from the current function */
  def typecheck ( e: Stmt, expected_type: Type ) {
    trace(e,e match {
      case AssignSt(RecordDeref(rec,"length"),_)
        if expandType(typecheck(rec)).isInstanceOf[ArrayType]
        => error("You cannot change the length of an array: "+e)
      case AssignSt(d,s)
        => if (!typeEquivalence(typecheck(d),typecheck(s)))
              error("Incompatible types in assignment: "+e)
      case CallSt(f,args)
        => st.lookup(f) match {
          case Some(FuncDeclaration(NoType(),params,_,_,_))
            => if (params.length != args.length)
                 error("Number of formal parameters does not much the number of arguments in call: "+e)
               else (args.map(typecheck) zip params).map {
                 case (atp,Bind(_,ptp))
                   => if (!typeEquivalence(atp,ptp))
                        error("The type of call argument ("+atp
                              +") does not match the type of the formal parameter: "+ptp)
               }
          case Some(VarDeclaration(FunctionType(params,NoType()),_,_))
            => if (params.length != args.length)
                 error("Number of formal parameters does not much the number of arguments in call: "+e)
               else (args.map(typecheck) zip params).map {
                 case (atp,ptp)
                   => if (!typeEquivalence(atp,ptp))
                        error("The type of call argument ("+atp
                              +") does not match the type of the formal parameter: "+ptp)
               }
          case Some(_) => error("Not a procedure: "+f)
          case _ => error("Undefined procedure: "+f)
        }
      case ReadSt(args)
        => for ( arg <- args ) {
              val t = typecheck(arg)
              if (!typeEquivalence(t,BooleanType())
                  && !typeEquivalence(t,IntType())
                  && !typeEquivalence(t,FloatType())
                  && !typeEquivalence(t,StringType()))
                 error("Expected primitive type in READ statement: "+e)
          }
      case PrintSt(args)
        => for ( arg <- args ) {
              val t = typecheck(arg)
              if (!typeEquivalence(t,BooleanType())
                  && !typeEquivalence(t,IntType())
                  && !typeEquivalence(t,FloatType())
                  && !typeEquivalence(t,StringType()))
                 error("Expected primitive type in WRITE statement: "+e)
          }
      case IfSt(p,a,b)
        => if (!typeEquivalence(typecheck(p),BooleanType()))
              error("Expected a boolean in IF test: "+p)
           typecheck(a,expected_type)
           if (b != null)
              typecheck(b,expected_type)
      case WhileSt(p,s)
        => if (!typeEquivalence(typecheck(p),BooleanType()))
              error("Expected a boolean in WHILE test: "+p)
           typecheck(s,expected_type)
      case LoopSt(s)
        => typecheck(s,expected_type)
      case ForSt(v,a,b,c,s)
        => if (!typeEquivalence(typecheck(a),IntType()))
              error("initial value in FOR loop must be integer: "+a)
           if (!typeEquivalence(typecheck(b),IntType()))
              error("step in FOR loop must be integer: "+b)
           if (!typeEquivalence(typecheck(c),IntType()))
              error("final value in FOR loop must be integer: "+c)
           st.begin_scope()
           st.insert(v,VarDeclaration(IntType(),0,0))
           typecheck(s,expected_type)
           st.end_scope()
      case ExitSt() => ;
      case ReturnSt()
        => if (!typeEquivalence(expected_type,NoType()))
              error("Expected a returned value of a non-void type: "+e)
      case ReturnValueSt(u)
        => if (typeEquivalence(expected_type,NoType()))
              error("Cannot return a value from a procedure: "+e)
           val tp = typecheck(u)
           if (!typeEquivalence(expected_type,tp))
              error("Expected a returned value of a different type: "+e)
      case BlockSt(dl)
        => st.begin_scope()
           dl.foreach {
             case Left(d) => typecheck(d)
             case Right(s) => typecheck(s,expected_type)
           }
           st.end_scope()
    } )
  }

  /** typecheck a definition */
  def typecheck ( e: Definition ) {
    trace(e,e match {
      case TypeDef(n,tp)
        => st.insert(n,TypeDeclaration(tp))
      case VarDef(v,tp,u)
        => if (tp == AnyType())
              st.insert(v,VarDeclaration(typecheck(u),0,0))
           else if (u != null && !typeEquivalence(typecheck(u),tp))
                   error("Incompatible types in variable declaration: "+e)
           else st.insert(v,VarDeclaration(tp,0,0))
      case FuncDef(f,ps,ot,b)
        => st.insert(f,FuncDeclaration(ot,ps,"",0,0))
           st.begin_scope()
           ps.foreach{ case Bind(v,tp) => st.insert(v,VarDeclaration(tp,0,0)) }
           typecheck(b,ot)
           st.end_scope()
    } )
  }

  /** typecheck the main program */
  def typecheck ( e: Program ) {
    typecheck(e.body,NoType())
  }
}
