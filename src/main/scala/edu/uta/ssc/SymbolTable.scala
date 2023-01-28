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


/** A symbol table with nested scopes */
class SymbolTable[T] {
  var symbol_table: List[List[(String,T)]] = Nil

  /** true if the item exists in the symbol table */
  def exists ( key: String ): Boolean = {
    val ds = for ( s <- symbol_table;
                   (n,d) <- s if n.equals(key)
                 ) yield d
    ds != Nil
  }

  /** lookup for an item in the symbol table */
  def lookup ( key: String ): Option[T] = {
    val ds = for ( s <- symbol_table;
                   (n,d) <- s if n.equals(key)
                 ) yield d
    ds match {
      case c::cs => Some(c)
      case _ => None
    }
  }

  /** insert a new item in the symbol table */
  def insert ( key: String, value: T ) {
    symbol_table match {
      case c::cs => symbol_table = ((key,value)::c)::cs
      case _ => throw new Error("Empty scope")
    }
  }

  /** replace an existing item in the symbol table */
  def replace ( key: String, value: T ) {
    symbol_table = symbol_table.map(_.map( b => if (b._1.equals(key))
                                                   (key,value)
                                                else b ))
  }

  /** start a new scope */
  def begin_scope () {
    symbol_table = List()::symbol_table
  }

  /** pop the last scope */
  def end_scope () {
    symbol_table match {
      case c::cs => symbol_table = cs
      case _ => throw new Error("Empty scope")
    }
  }

  /** return the current scope as a list of pairs */
  def current_scope (): List[(String,T)]
    = symbol_table.head

  override def toString: String = {
    symbol_table.toString
  }

}
