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

object Normalizer {

  /* convert the IR e into a list of IRs that do not contain any Seq or ESeq IRs */
  def normalize ( e: IRexp ): (IRexp,List[IRstmt]) =
    e match {
      case Mem(a)
        => val (na,s) = normalize(a)
           (Mem(na),s)
      case Indexed(a,i)
        => val (na,as) = normalize(a)
           val (ni,is) = normalize(i)
           (Indexed(na,ni),as++is)
      case Binop(op,l,r)
        => val (nl,ls) = normalize(l)
           val (nr,rs) = normalize(r)
           (Binop(op,nl,nr),ls++rs)
      case Unop(op,a)
        => val (na,s) = normalize(a)
           (Unop(op,na),s)
      case Call(f,l,as)
        => val (nl,ls) = normalize(l)
           val nas = as.map(normalize)
           ( Call(f,nl,nas.map(_._1)),
             ls ++ nas.flatMap(_._2) )
      case ESeq(s,a)
        => val ss = normalize(s)
           val (na,as) = normalize(a)
           (na,ss++as)
      case Allocate(tp,a)
        => val (na,s) = normalize(a)
           (Allocate(tp,na),s)
      case Coerce(a,t1,t2)
        => val (na,s) = normalize(a)
           (Coerce(na,t1,t2),s)
      case _ => (e,List())
  }

  def normalize ( e: IRstmt ): List[IRstmt] =
    e match {
      case Move(x,y)
        => val (nx,xs) = normalize(x)
           val (ny,ys) = normalize(y)
           xs ++ ys :+ Move(nx,ny)
      case CJump(c,l)
        => val (nc,s) = normalize(c)
           s :+ CJump(nc,l)
      case Seq(s)
        => s.flatMap(normalize)
      case CallP(f,l,as)
        => val (nl,ls) = normalize(l)
           val nas = as.map(normalize)
           ls ++ nas.flatMap(_._2) :+ CallP(f,nl,nas.map(_._1))
      case SystemCall(f,a)
        => val (na,s) = normalize(a)
           s :+ SystemCall(f,na)
      case Return(u)
        => val (nu,s) = normalize(u)
           s :+ Return(nu)
      case _ => List(e)
  }
}
