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

import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.token.StdTokens
import scala.util.parsing.input.CharArrayReader
import scala.util.matching.Regex

trait MyTokens extends StdTokens {
  case class DoubleLit ( chars: String ) extends Token
  case class CharLit ( chars: String ) extends Token
  case class InfixOpr ( chars: String ) extends Token
  case class IncrOpr ( chars: String ) extends Token
}

class MyLexical extends StdLexical with MyTokens {
  /* a parser for regular expressions */
  def regex ( r: Regex ): Parser[String]
      = new Parser[String] {
            def apply ( in: Input )
                = r.findPrefixMatchOf(in.source.subSequence(in.offset,in.source.length)) match {
                        case Some(matched)
                          => Success(in.source.subSequence(in.offset,in.offset+matched.end).toString,
                                     in.drop(matched.end))
                        case None => Failure("string matching regex `"+r+"' expected but "+in.first+" found",in)
                  }
      }

  override def token: Parser[Token] = incrOpr | infixOpr | doubleLit | charLit | super.token

  /* floating point numbers */
  def doubleLit: Parser[Token]
      = regex("""[0-9]*[.][0-9]+([eE][+-]?[0-9]+)?[FfDd]?""".r) ^^ { DoubleLit }

  /* character literal */
  def charLit: Parser[Token]
      = regex("""'[^']'""".r) ^^ { CharLit }

  /* an infix operator can be any sequence of special chars, except delimiters, etc */ 
  def infixOpr: Parser[Token]
      = regex("""[^\s\w$()\[\]{}'"`.;,\\/]+""".r) ^^
        { s => if (delimiters.contains(s)) Keyword(s) else InfixOpr(s) }

  def incrOpr: Parser[Token]
      = regex("""[^\s\w$()\[\]{}'"`.;,\\/\=]+\=""".r) ^^
        { s => if (delimiters.contains(s)) Keyword(s) else IncrOpr(s) }
}

object Parser extends StandardTokenParsers {
  override val lexical = new MyLexical

  var type_vars: List[List[String]] = Nil

  lexical.delimiters ++= List( "(" , ")" , "[", "]", "{", "}", "," , ":", ";", ".", "=>", "=", "->", "<-",
                               "||", "&&", "!", "==", "<=", ">=", "<", ">", "!=", "+", "-", "*", "/", "%",
                               ":=", "#", "^", "|", "&" )

  lexical.reserved ++= List( "and", "array", "boolean", "by", "def", "div", "else", "equal", "exit", "false", "float", "for",
                             "function", "if", "int", "loop", "mod", "not", "or", "print", "read", "return", "to", "type",
                             "var", "while", "true", "string" )

  /* groups of infix operator precedence, from low to high */
  val operator_precedence: List[Parser[String]]
      = List( "||", "^", "&&"|"&", "<="|">="|"<"|">", "=="|"<>", "+"|"-", "*"|"/"|"%" )

  val operators = Map( "||" -> "or", "&&" -> "and", "<=" -> "leq", ">=" -> "geq", "<" -> "lt", ">" -> "gt", "%" -> "mod",
                       "<>" -> "neq", "==" -> "eq", "+" -> "plus", "-" -> "minus", "*" -> "times", "/" -> "div" )

  /* all infix operators not listed in operator_precedence have the same highest precedence */  
  val infixOpr: Parser[String]
      = accept("infix operator",{ case t: lexical.InfixOpr => t.chars })
  val incrOpr: Parser[String]
      = accept("increment operator",{ case t: lexical.IncrOpr => t.chars })
  val precedence: List[Parser[String]]
      = operator_precedence :+ infixOpr
  val allInfixOpr: Parser[String]
      = operator_precedence.fold(infixOpr)(_|_)

  /* group infix operations into terms based on the operator precedence, from low to high */
  def terms ( level: Int ): Parser[(Expr,Expr)=>Expr]
      = precedence(level) ^^
        { op => (x:Expr,y:Expr) => BinOpExp(operators(op),x,y) }
  def infix ( level: Int ): Parser[Expr]
      = if (level >= precedence.length) factor
        else infix(level+1) * terms(level)

  def fromRaw ( s: String ): String = s.replace("""\n""","\n")
        
  def expr: Parser[Expr]
      = infix(0) | factor

  def char: Parser[String]
      = accept("char literal",{ case t: lexical.CharLit => t.chars })

  def int: Parser[Int]
      = numericLit ^^ { _.toInt }

  def float: Parser[Float]
      = accept("float literal",{ case t: lexical.DoubleLit => t.chars.toFloat })

 def factorList ( e: Expr ): Parser[Expr]
     = ( "[" ~ expr ~ "]" ^^
         { case _~i~_ => ArrayDeref(e,i) }
       | "." ~ ident ^^
         { case _~a => RecordDeref(e,a) }
       | "#" ~ int ^^
         { case _~n => TupleDeref(e,n) }
       )

 def factor: Parser[Expr]
      = term ~ rep( factorList(IntConst(0)) ) ^^
        { case e~s => s.foldLeft[Expr](e) {
                          case (r,RecordDeref(_,a))
                            => RecordDeref(r,a)
                          case (r,ArrayDeref(_,n))
                            => ArrayDeref(r,n)
                          case (r,TupleDeref(_,s))
                            => TupleDeref(r,s)
                          case (r,_) => r } }

 def lvalue: Parser[Expr]
    = ( term ~ rep1( factorList(IntConst(0)) ) ^^
        { case e~s => s.foldLeft[Expr](e) {
                          case (r,RecordDeref(_,a))
                            => RecordDeref(r,a)
                          case (r,ArrayDeref(_,n))
                            => ArrayDeref(r,n)
                          case (r,TupleDeref(_,s))
                            => TupleDeref(r,s)
                          case (r,_) => r }
        }
      | ident ^^ { s => Var(s) }
      | failure("Wrong l-value")
      )

  def term: Parser[Expr]
      = ( "true" ^^^ BooleanConst(true)
        | "false" ^^^ BooleanConst(false)
        | float ^^
          { s => FloatConst(s) }
        | int ^^
          { s => IntConst(s) }
        | stringLit ^^
          { s => StringConst(fromRaw(s)) }
        | "array" ~ "(" ~ expr ~ "," ~ expr ~ ")" ^^
          { case _~_~e1~_~e2~_ => ArrayGen(e1,e2) }
        | ident ~ "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case f~_~es~_ => CallExp(f,es) }
        | ident ^^
          { s => Var(s) }
        | "-" ~ expr ^^
          { case _~e => UnOpExp("minus",e) }
        | "NOT" ~ expr ^^
          { case _~e => UnOpExp("NOT",e) }
        | "{" ~ repsep( ident ~ "=" ~ expr, "," ) ~ "}" ^^
          { case _~rl~_ => RecordExp(rl.map{ case v~_~e => Bind(v,e) }) }
        | "[" ~ repsep( expr, "," ) ~ "]" ^^
          { case _~es~_ => ArrayExp(es) }
        | "(" ~ ")" ^^^ NullExp()
        | "(" ~ expr ~ ")" ^^
          { case _~e~_ => e }
        | "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case _~es~_ => TupleExp(es) }
        | "function" ~ "(" ~ formals ~ ")" ~ ":" ~ stype ~ block ^^
          { case _~_~fs~_~_~t~b => FunctionExp(fs,t,b) }
        | failure("illegal start of expression")
        )

  def stmt: Parser[Stmt]
      = ( lvalue ~ "=" ~ expr ^^
          { case d~_~e => AssignSt(d,e) }
        | ident ~ "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case f~_~es~_ => CallSt(f,es) }
        | block ^^ { b => b }
        | "read" ~ "(" ~ repsep( lvalue, "," ) ~ ")" ^^
          { case _~_~es~_ => ReadSt(es) }
        | "print" ~ "(" ~ repsep( expr, "," ) ~ ")" ^^
          { case _~_~es~_ => PrintSt(es) }
        | "if" ~ "(" ~ expr ~ ")" ~ stmt ~ opt( "else" ~ stmt ) ^^
          { case _~_~p~_~st~Some(_~se) => IfSt(p,st,se)
            case _~_~p~_~st~_ => IfSt(p,st,null) }
        | "while" ~ "(" ~ expr ~ ")" ~ stmt ^^
          { case _~_~e~_~s => WhileSt(e,s) }
        | "loop" ~ stmt ^^
          { case _~s => LoopSt(s) }
        | "for" ~ "(" ~ ident ~ "=" ~ expr ~ "to" ~ expr ~ opt( "by" ~ expr ) ~ ")" ~ stmt ^^
          { case _~_~i~_~e1~_~e2~Some(_~e3)~_~s => ForSt(i,e1,e2,e3,s)
            case _~_~i~_~e1~_~e2~_~_~s => ForSt(i,e1,e2,IntConst(1),s) }
        | "exit" ^^^ ExitSt()
        | "return" ~ opt( expr ) ^^
          { case _~Some(e) => ReturnValueSt(e)
            case _~_ => ReturnSt() }
        )

  def stype: Parser[Type]
      = ( "int" ^^^ IntType()
        | "float" ^^^ FloatType()
        | "string" ^^^ StringType()
        | "boolean" ^^^ BooleanType()
        | ident ~ opt("[" ~ rep1sep(stype,",") ~ "]") ^^
          { case v~None
              => if (type_vars.foldLeft(false){ case (r,s) => r || s.contains(v) })
                   TypeParameter(v)
                 else NamedType(v,Nil)
            case v~Some(_~vs~_) => NamedType(v,vs) }
        | "array" ~ "[" ~ stype ~ "]" ^^
          { case _~_~t~_ => ArrayType(t) }
        | "{" ~ formals ~ "}" ^^
          { case _~fs~_ => RecordType(fs) }
        | "(" ~ repsep( stype, "," ) ~ ")" ~ "->" ~ stype ^^
          { case _~ts~_~_~t => FunctionType(ts,t) }
        | "(" ~ ")" ^^^ NoType()
        | "(" ~ stype ~ ")" ^^
          { case _~t~_ => t }
        | "(" ~ repsep( stype, "," ) ~ ")" ^^
          { case _~ts~_ => TupleType(ts) }
        )

  def formals: Parser[List[Bind[Type]]]
      = repsep( ident ~ ":" ~ stype, "," ) ^^
        { _.map{ case v~_~t => Bind(v,t) } }

  def push_tvars ( tvars_parser: Parser[List[String]] ): Parser[List[String]]
    = tvars_parser ^^ { s => type_vars = s::type_vars; s }

  def pop_tvars () { type_vars = type_vars.tail }

  def defn: Parser[Definition]
      = ( "var" ~ ident ~ opt(":" ~ stype) ~ opt("=" ~ expr) ^^
          { case _~f~Some(_~t)~Some(_~e) => VarDef(f,t,e)
            case _~f~None~Some(_~e) => VarDef(f,AnyType(),e)
            case _~f~Some(_~t)~None => VarDef(f,t,NullExp())
            case _ => throw new Exception("A var declaration needs a type or a value or both") }
        | "type" ~ ident ~ opt("[" ~ push_tvars(rep1sep(ident,",")) ~ "]") ~ "=" ~ stype ^^
          { case _~v~None~_~t => TypeDef(Nil,v,t)
            case _~v~Some(_~vs~_)~_~t
              => { val d = TypeDef(vs,v,t); pop_tvars(); d } }
        | "def" ~ ident ~ opt("[" ~ push_tvars(rep1sep(ident,",")) ~ "]")
                ~ "(" ~ formals ~ ")" ~ opt(":" ~ stype) ~ block ^^
          { case _~f~None~_~fs~_~Some(_~t)~b => FuncDef(Nil,f,fs,t,b)
            case _~f~None~_~fs~_~None~b => FuncDef(Nil,f,fs,NoType(),b)
            case _~f~Some(_~vs~_)~_~fs~_~Some(_~t)~b
              => { val d = FuncDef(vs,f,fs,t,b); pop_tvars(); d }
            case _~f~Some(_~vs~_)~_~fs~_~None~b
              => { val d = FuncDef(vs,f,fs,NoType(),b); pop_tvars(); d } }
        )

  def program: Parser[Program]
      = rep(defOrStmt) ^^
        { ds => Program(BlockSt(ds)) }

  def sem: Parser[Option[String]] = opt( ";" )

  def defOrStmt: Parser[Either[Definition,Stmt]]
    = ( defn ~ sem ^^
        { case d~_ => Left(d) }
      | stmt ~ sem ^^
        { case s~_ => Right(s) }
      )

  def block: Parser[BlockSt]
      = "{" ~ rep(defOrStmt) ~ "}" ^^
        { case _~ds~_ => BlockSt(ds) }

  def string_reader ( text: String)
    = new lexical.Scanner(new CharArrayReader(text.toArray))

  /** Parse an SSC line */
  def parse_line ( line: String ): Program
      = phrase (program) (string_reader(line)) match {
          case Success(e,_)
            => e:Program
          case m => println(m); Program(BlockSt(Nil))
        }

  /** Parse an SSC program */
  def parse ( file: String ): Program
      = parse_line(io.Source.fromFile(file).mkString)
}
