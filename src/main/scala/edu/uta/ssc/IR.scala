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


sealed abstract class IRtype
case class BooleanIRtype () extends IRtype
case class ByteIRtype () extends IRtype
case class IntIRtype () extends IRtype
case class FloatIRtype () extends IRtype
case class StringIRtype () extends IRtype
case class VoidIRtype () extends IRtype
case class LabelIRtype () extends IRtype
case class AddressIRtype ( address: IRtype ) extends IRtype
case class NamedIRtype ( name: String, args: List[IRtype] ) extends IRtype
case class VecIRtype ( elem: IRtype ) extends IRtype
case class RecordIRtype ( elems: List[Bind[IRtype]] ) extends IRtype
case class TupleIRtype ( elems: List[IRtype] ) extends IRtype
case class FunctionIRtype ( formal_params: List[IRtype], result_type: IRtype ) extends IRtype
case class TypeVarIRtype ( type_var: String ) extends IRtype

/** Intermediate Representations for Expressions */
sealed abstract class IRexp
case class BooleanValue ( value: Boolean ) extends IRexp
case class IntValue ( value: Int ) extends IRexp
case class FloatValue ( value: Float ) extends IRexp
case class StringValue ( value: String ) extends IRexp
case class NullValue () extends IRexp
case class Address ( value: String ) extends IRexp
case class VoidValue () extends IRexp
case class FramePointer () extends IRexp
/** a closure is a pair of a function with a static link */
case class Closure ( function_name: String, static_link: IRexp ) extends IRexp
/** the address of an element of a composite type (tuple, vector, etc) */
case class Indexed ( address: IRexp, offset: IRexp ) extends IRexp
/** the size of type in bytes */
case class TypeSize ( object_type: IRtype ) extends IRexp
/** allocate size number of bytes in the heap and return the object address */
case class Allocate ( otype: IRtype, size: IRexp ) extends IRexp
/** get the memory content at a given address */
case class Mem ( address: IRexp ) extends IRexp
/** binary operations: GT, LT, EQ, GE, LE, NE, PLUS, MINUS, TIMES, SLASH, DIV, MOD, AND, OR */
case class Binop ( op: String, left: IRexp, right: IRexp ) extends IRexp
/** unary operations: MINUS, NOT */
case class Unop ( op: String, operand: IRexp ) extends IRexp
/** call a function by providing a static link and by passing arguments and return back the result */
case class Call ( address: IRexp, static_link: IRexp, arguments: List[IRexp] ) extends IRexp
/** evaluate the statement and return the value */
case class ESeq ( stmt: IRstmt, value: IRexp ) extends IRexp
/** used in polymorphic functions */
case class Coerce ( e: IRexp, from_type: IRtype, to_type: IRtype ) extends IRexp

/** Intermediate Representations for Statements */
sealed abstract class IRstmt
/** store the source to the destination (a Mem or a Reg IRexp) */
case class Move ( destination: IRexp, source: IRexp ) extends IRstmt
/** define a label to be the current address */
case class Label ( name: String ) extends IRstmt
/** jump to a label */
case class Jump ( name: String ) extends IRstmt
/** jump to a label if condition is true */
case class CJump ( condition: IRexp, label: String ) extends IRstmt
/** evaluate a sequence of statements */
case class Seq ( stmts: List[IRstmt] ) extends IRstmt
/** call a procedure by providing a static link and by passing arguments */
case class CallP ( address: IRexp, static_link: IRexp, arguments: List[IRexp] ) extends IRstmt
/** a system call can be: READ_INT, READ_FLOAT, WRITE_INT, WRITE_FLOAT, WRITE_BOOL, WRITE_STRING */
case class SystemCall ( name: String, arg: IRexp ) extends IRstmt
/** return from a function/procedure */
case class Return ( value: IRexp ) extends IRstmt
case class Assert ( condition: IRexp ) extends IRstmt


sealed abstract class IRdecl
case class IRtypeDecl ( label: String, type_vars: List[String], isType: IRtype ) extends IRdecl
case class IRfuncDecl ( label: String, frame: List[IRtype], type_vars: List[String], formal_params: List[IRtype],
                        result_type: IRtype, level: Int, body: List[IRstmt] ) extends IRdecl
