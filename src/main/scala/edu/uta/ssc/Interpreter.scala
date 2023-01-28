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

import scala.io.StdIn._

/** An AST interpreter */
object Interpreter {

  /** The environment that binds names (of variables & functions) to their values */
  type Env = List[Bind[Value]]

  /** The domain of values, which are the target of the interpreter */
  sealed abstract class Value
  case class IntVal ( value: Int ) extends Value
  case class FloatVal ( value: Float ) extends Value
  case class BooleanVal ( value: Boolean ) extends Value
  case class StringVal ( value: String ) extends Value
  case class Void () extends Value
  case class VectorVal ( value: Array[Value] ) extends Value
  case class RecordVal ( value: List[Bind[Value]] ) extends Value
  case class Closure ( args: List[String], body: Stmt, var env: Env ) extends Value

  /** Functions return values by throwing this exception */
  case class ReturnValue( value: Value ) extends Exception

  val true_val = BooleanVal(true)
  var exit = false

  /** Get the value of name from the environment */
  def lookup ( name: String, env: Env ): Value
    = env.find{ case Bind(n,_) => n == name } match {
        case Some(Bind(_,v))
          => v
        case _ => throw new Error("Undefined name: " + name)
    }

  /** Update the value of the name in the environment */
  def replace ( name: String, value: Value, env: Env ) {
    env.find{ case Bind(n,_) => n == name } match {
      case Some(p)
        => p.value = value
      case _ => throw new Error("Undefined name: " + name)
    }
  }

  /** Coerce a value to a float */
  def toFloat ( v: Value ): Float = {
    v match {
      case FloatVal(x)
        => x
      case IntVal(x)
        => x.toFloat
      case _ => throw new Error("Cannot coerce "+string(v)+" to a float")
    }
  }

  /** Print the value into a string */
  def string ( v: Value ): String =
    v match {
      case IntVal(n)
        => n.toString
      case FloatVal(n)
        => n.toString
      case BooleanVal(b)
        => if (b) "true" else "false"
      case StringVal(s)
        => "\""+s+"\""
      case Void()
        => "void"
      case RecordVal(rs)
        => rs.map{ case Bind(n,w) => n+" = "+string(w) }.mkString("{ ",", "," }")
      case VectorVal(elems)
        => elems.map(string).mkString("( ",", "," )")
      case Closure(args,_,_)
        => "function of ( "+args.mkString(",")+" )"
      case _ => throw new Error("Expected a value to print: " + v)
    }

  /** Evaluate an expression AST e under the binding environment env */
  def eval ( e: Expr, env: Env ): Value =
    e match {
      case IntConst(n)
        => IntVal(n)
      case FloatConst(n)
        => FloatVal(n)
      case StringConst(s)
        => StringVal(s)
      case BooleanConst(b)
        => BooleanVal(b)
      case NullExp()
        => Void()
      case BinOpExp("and",l,r)
        => eval(l,env) match {
              case BooleanVal(true) => eval(r,env)
              case b => b
           }
      case BinOpExp("or",l,r)
        => eval(l,env) match {
            case BooleanVal(false) => eval(r,env)
            case b => b
         }
      case BinOpExp("eq",l,r)
        => BooleanVal(eval(l,env) == eval(r,env))
      case BinOpExp("neq",l,r)
        => BooleanVal(eval(l,env) != eval(r,env))
      case BinOpExp(op,l,r)
        => val lv = eval(l,env)
           val rv = eval(r,env)
           (lv,rv) match {
             case (IntVal(x),IntVal(y))
               => op match {
                    case "plus" => IntVal(x+y)
                    case "minus" => IntVal(x-y)
                    case "times" => IntVal(x*y)
                    case "div" => IntVal(x/y)
                    case "mod" => IntVal(x%y)
                    case "leq" => BooleanVal(x<=y)
                    case "lt" => BooleanVal(x<y)
                    case "geq" => BooleanVal(x>=y)
                    case "gt" => BooleanVal(x>y)
                    case _ => throw new Error("Uknown operation "+op)
             }
             case _
               => val x = toFloat(lv)
                  val y = toFloat(rv)
                  op match {
                    case "plus" => FloatVal(x+y)
                    case "minus" => FloatVal(x-y)
                    case "times" => FloatVal(x*y)
                    case "div" => FloatVal(x/y)
                    case "mod" => FloatVal(x%y)
                    case "leq" => BooleanVal(x<=y)
                    case "lt" => BooleanVal(x<y)
                    case "geq" => BooleanVal(x>=y)
                    case "gt" => BooleanVal(x>y)
                    case _ => throw new Error("Uknown operation "+op)
                  }
           }
      case UnOpExp("minus",u)
        => val uv = eval(u,env)
           uv match {
             case IntVal(x)
               => IntVal(-x)
             case FloatVal(x)
               => FloatVal(-x)
             case _ => throw new Error("Value "+string(uv)+" is not numerical")
           }
      case UnOpExp("not",u)
        => val uv = eval(u,env)
           uv match {
             case BooleanVal(x)
               => BooleanVal(!x)
             case _ => throw new Error("Value "+string(uv)+" is not boolean")
           }
      case LvalExp(lv)
        => eval(lv,env)
      case CallExp(f,args)
        => lookup(f,env) match {
              case Closure(params,body,cenv)
                 => if (params.length != args.length)
                      throw new Error("Number of formal parameters does not much the number of arguments in call: "+e)
                    else try eval(body,(params zip args.map(eval(_,env))).map{ case (n,v) => Bind(n,v) }++cenv) catch {
                         case ReturnValue(v) => return v
                    }
                    throw new Error("Returned from function "+f+" without a value")
              case _ => throw new Error("Undefined function: "+f)
          }
      case RecordExp(cs)
        => RecordVal(cs.map{ case Bind(n,v) => Bind(n,eval(v,env)) })
      case TupleExp(cs)
        => VectorVal(cs.map(eval(_,env)).toArray)
      case ArrayGen(len,v)
        => val vv = eval(v,env)
           eval(len,env) match {
              case IntVal(n)
                => VectorVal((1 to n).map{ _ => vv }.toArray)
              case _ => throw new Error("Wrong array construction: "+e)
           }
      case ArrayExp(cs)
        => VectorVal(cs.map(eval(_,env)).toArray)
      case FunctionExp(fs,_,b)
        => Closure(fs.map{ case Bind(v,_) => v },b,env)
      case _ => throw new Error("Unrecognized AST expression: "+e)
    }

  /** Evaluate an Lvalue AST under the binding environment env */
  def eval ( e: Lvalue, env: Env ): Value =
    e match {
      case Var(name)
        => lookup(name,env)
      case ArrayDeref(array,index)
        => (eval(array,env),eval(index,env)) match {
              case (VectorVal(a),IntVal(i))
                => a(i)
              case (VectorVal(_),x)
                => throw new Error("Array index must be integer: "+x)
              case (x,_)
                => throw new Error("Array indexing can only be done on arrays: "+x)
           }
      case RecordDeref(rec,attr)
        => eval(rec,env) match {
              case RecordVal(rs)
                => rs.flatMap{ case Bind(n,v) => if (n == attr) List(v) else Nil }.head
              case VectorVal(a) if attr == "length"
                => IntVal(a.length)
              case x => throw new Error("Record projection can only be done on records: "+x)
           }
      case TupleDeref(t,i)
        => eval(t,env) match {
              case VectorVal(a) => a(i)
              case x => throw new Error("Tuple indexing can only be done on tuples: "+x)
           }
    }

  /** Replace the content of an Lvalue with a new value */
  def assign ( e: Lvalue, v: Value, env: Env ) {
    e match {
      case Var(name)
        => replace(name,v,env)
      case ArrayDeref(array, index)
        => (eval(array,env), eval(index,env)) match {
              case (VectorVal(a), IntVal(i))
                => a(i) = v
              case (VectorVal(_), x)
                => throw new Error("Array index must be integer: " + x)
              case (x, _)
                => throw new Error("Array indexing can only be done on arrays: " + x)
           }
      case RecordDeref(rec,attr)
        => eval(rec,env) match {
              case RecordVal(rs)
                => rs.foreach{ case b@Bind(n,_) => if (n == attr) b.value = v }
              case VectorVal(_) if attr == "length"
                => throw new Error("Cannot change the vector length: "+e)
              case x => throw new Error("Record projection can only be done on records: "+x)
           }
      case TupleDeref(t,i)
        => eval(t,env) match {
              case VectorVal(a)
                => a(i) = v
              case x => throw new Error("Tuple indexing can only be done on tuples: " + x)
           }
    }
  }

  /** Evaluate a statement AST under the binding environment env */
  def eval ( e: Stmt, env: Env ) {
    if (e != null)
    e match {
      case AssignSt(d,s)
        => assign(d,eval(s,env),env)
      case CallSt(f,args)
        => lookup(f,env) match {
              case Closure(params,body,cenv)
                => if (params.length != args.length)
                     throw new Error("Number of formal parameters does not much the number of arguments in call: "+e)
                   else try eval(body,(params zip args.map(eval(_,env))).map{ case (n,v) => Bind(n,v) }++cenv) catch {
                case ReturnValue(Void()) => ;
                case ReturnValue(v) => throw new Error("procedure "+f+" should not return a value: "+v)
                   }
              case _ => throw new Error("Undefined procedure: "+f)
           }
      case ReadSt(args)
        => for ( arg <- args )
              eval(arg,env) match {
                case IntVal(_)
                  => assign(arg,IntVal(readInt),env)
                case FloatVal(_)
                  => assign(arg,FloatVal(readFloat),env)
                case StringVal(_)
                  => assign(arg,StringVal(readLine),env)
                case _ => throw new Error("Expected primitive type in READ statement: "+arg)
              }
      case PrintSt(args)
        => for ( arg <- args )
              eval(arg,env) match {
                case StringVal(s)
                  => print(s)
                case v => print(string(v))
              }
           println
      case IfSt(p,a,b)
        => if (eval(p,env) == true_val)
             eval(a,env)
           else eval(b,env)
      case WhileSt(p,s)
        => while (!exit && eval(p,env) == true_val)
             eval(s,env)
           exit = false
      case LoopSt(s)
        => while (!exit)
             eval(s,env)
           exit = false
      case ForSt(v,a,b,c,s)
        => (eval(a,env),eval(b,env),eval(c,env)) match {
                  case (IntVal(av), IntVal(bv), IntVal(cv))
                    => val nenv: Env = Bind(v,IntVal(av).asInstanceOf[Value])::env
                       for (i <- av to bv by cv if !exit) {
                          replace(v,IntVal(i).asInstanceOf[Value],nenv)
                          eval(s,nenv)
                       }
                       exit = false
                  case _ => throw new Error("Values in FOR loop must be integers: "+e)
                  }
      case ExitSt()
        => exit = true
      case ReturnSt()
        => throw ReturnValue(Void())
      case ReturnValueSt(u)
        => throw ReturnValue(eval(u,env))
      case BlockSt(dl)
        => var nenv = env
           dl.foreach {
             case Left(d) => nenv = eval(d,nenv)
             case Right(s) => eval(s,nenv)
           }
      case _ => throw new Error("Unrecognized AST statement: "+e)
    }
  }

  /** Evaluate a definition and extend the current environment */
  def eval ( e: Definition, env: Env ): Env =
    e match {
      case TypeDef(_,_)
        => env
      case VarDef(v,_,u)
        => Bind(v,eval(u,env))::env
      case FuncDef(f,ps,_,b)
        => val closure = Closure(ps.map{ case Bind(v,_) => v },b,env)
           val nenv: Env = Bind(f,closure.asInstanceOf[Value])::env
           closure.env = nenv   // the closure environment must contain f to allow recursion
           nenv
    }

  /** Evaluate the main program */
  def eval ( e: Program ) {
    eval(e.body,Nil)
  }

  /** An read-eval-print interpreter that reads and evaluates SSC expressions and statements */
  def main ( args: Array[String] ) {
    println("The SSC interpreter. Type quit to exit")
    println("Type =e to evaluate an SSC expression e; everything else is evaluated as a statement or declaration. ")
    var env: Env = List(Bind("res",IntVal(0)))
    val print_ast = args.length > 0 && args(0) == "ast"
    //val consoleReader = new scala.tools.jline.console.ConsoleReader()
    do try {
      //var line = consoleReader.readLine("> ")
      print("> ")
      var line = readLine()
      if (line == "quit")
        return
      val ep = line.nonEmpty && line(0) == '='
      if (ep)
        line = "res="+line.tail
      val program_ast = Parser.parse_line(line+";")
      if (print_ast)
        println(Pretty.print(program_ast.toString))
      program_ast.body match {
          case BlockSt(dl)
            => dl.foreach {
                  case Left(d) => env = eval(d,env)
                  case Right(s) => eval(s,env)
               }
      }
      if (ep)
        println("-> "+string(lookup("res",env)))
    } catch {
      case s: Error => System.err.println(s.getMessage)
      case s: Throwable => System.err.println(s)
    } while(true)
  }
}
