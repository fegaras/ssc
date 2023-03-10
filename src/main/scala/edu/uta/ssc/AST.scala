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

/** A name-value binding */
case class Bind[T] ( name: String, var value: T )


/** Abstract syntax tree for the main program */
case class Program ( body: BlockSt )

/** Abstract syntax trees for definitions */
sealed abstract class Definition
/** a type definition */
case class TypeDef ( typeParams: List[String], name: String, isType: Type ) extends Definition
/** a variable definition */
case class VarDef ( name: String, hasType: Type, value: Expr ) extends Definition
/** a function definition */
case class FuncDef ( typeParams: List[String], name: String, formal_params: List[Bind[Type]],
                     result_type: Type, body: BlockSt ) extends Definition

/** Abstract syntax trees for types */
sealed abstract class Type
case class IntType () extends Type
case class FloatType () extends Type
case class StringType () extends Type
case class BooleanType () extends Type
case class NamedType ( typename: String, args: List[Type] ) extends Type
case class ArrayType ( element_type: Type ) extends Type
case class RecordType ( components: List[Bind[Type]] ) extends Type
case class TupleType ( components: List[Type] ) extends Type
case class FunctionType ( formal_params: List[Type], result_type: Type ) extends Type
case class TypeParameter ( name: String ) extends Type
case class AnyType () extends Type
case class NoType () extends Type

/** Abstract syntax trees for expressions */
sealed abstract class Expr ( var tpe: Type = null )
case class Var ( name: String ) extends Expr
case class IntConst ( value: Int ) extends Expr
case class FloatConst ( value: Float ) extends Expr
case class StringConst ( value: String ) extends Expr
case class BooleanConst ( value: Boolean ) extends Expr
case class NullExp () extends Expr
case class BinOpExp ( op: String, left: Expr, right: Expr ) extends Expr
case class UnOpExp ( op: String, operand: Expr ) extends Expr
case class ArrayDeref ( array: Expr, index: Expr ) extends Expr
case class RecordDeref ( record: Expr, attribute: String ) extends Expr
case class TupleDeref ( tuple: Expr, index: Int ) extends Expr
case class CallExp ( name: String, arguments: List[Expr] ) extends Expr
case class RecordExp ( components: List[Bind[Expr]] ) extends Expr
case class ArrayExp ( elements: List[Expr] ) extends Expr
case class ArrayGen ( length: Expr, value: Expr ) extends Expr
case class TupleExp ( elements: List[Expr] ) extends Expr
case class FunctionExp ( formal_params: List[Bind[Type]], result_type: Type, body: BlockSt ) extends Expr

/** Abstract syntax trees for statements */
sealed abstract class Stmt
case class AssignSt ( destination: Expr, source: Expr ) extends Stmt
case class CallSt ( name: String, arguments: List[Expr] ) extends Stmt
case class ReadSt ( arguments: List[Expr] ) extends Stmt
case class PrintSt ( arguments: List[Expr] ) extends Stmt
case class IfSt ( condition: Expr, then_stmt: Stmt, else_stmt: Stmt ) extends Stmt
case class WhileSt ( condition: Expr, body: Stmt ) extends Stmt
case class LoopSt ( body: Stmt ) extends Stmt
case class ForSt ( variable: String, initial: Expr, last: Expr, increment: Expr, body: Stmt ) extends Stmt
case class ExitSt () extends Stmt
case class ReturnValueSt ( value: Expr ) extends Stmt
case class ReturnSt () extends Stmt
case class BlockSt ( content: List[Either[Definition,Stmt]] ) extends Stmt

/** Declarations for variables, types, and functions */
sealed abstract class Declaration
/** type declaration: has a type */
case class TypeDeclaration ( typeParams: List[String], hastype: Type ) extends Declaration
/** variable declaration: the type and the level/offset of a variable in a frame */
case class VarDeclaration ( vartype: Type, level: Int, offset: Int ) extends Declaration
/** function declaration: output type, formal parameters, code address,
 *  parent's code address, nesting level, and next available offset in a frame */
case class FuncDeclaration ( typeParams: List[String], outtype: Type, params: List[Bind[Type]],
                             label: String, level: Int, available_offset: Int ) extends Declaration


object AST {

  /** apply f to every type in tp */
  def apply ( tp: Type, f: Type => Type ): Type
    = tp match {
         case NamedType(n,ts)
           => NamedType(n,ts.map(f))
         case ArrayType(t)
           => ArrayType(f(t))
         case RecordType(ts)
           => RecordType(ts.map { case Bind(n,t) => Bind(n,f(t)) })
         case TupleType(ts)
           => TupleType(ts.map(f))
         case FunctionType(ts,ot)
           => FunctionType(ts.map(f),f(ot))
         case _ => tp
      }

  /** fold over expressions */
  def accumulate[T] ( e: Type, f: Type => T, acc: (T,T) => T, zero: T ): T
    = e match {
        case NamedType(n,ts)
          => ts.map(f).fold(zero)(acc)
        case ArrayType(t)
           => f(t)
        case RecordType(ts)
           => ts.map { case Bind(n,t) => f(t) }.fold(zero)(acc)
         case TupleType(ts)
           => ts.map(f).fold(zero)(acc)
         case FunctionType(ts,ot)
           => ts.map(f).fold(f(ot))(acc)
         case _ => zero
      }
}
