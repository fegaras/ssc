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

import java.io.PrintStream

object SSC {
  val debug = false

  def main ( args: Array[String] ) {
    for ( file <- args ) {
      if (args.length > 1)
        println("... compiling "+file)
      val program_ast = Parser.parse(file)
      program_ast match {
        case Program(BlockSt(Nil))
          => sys.exit(-1)
        case _ =>;
      }
      if (debug)
        println(Pretty.print(program_ast.toString))
      TypeInference.trace_type_inference = false
      TypeInference.type_inference(program_ast)
      val ir = CodeGenerator.code(program_ast)
      if (debug)
        ir.foreach { case Bind(_,a) => println(Pretty.print(a.toString)) }
      val stream = new PrintStream(file.dropRight(3)+"ll")
      val llvm = new LLVM(stream)
      llvm.emit(ir)
      stream.close()
    }
  }
}
