# SSC: A compiler from a simple programming language to LLVM

Requires Scala 2.12, [LLVM 14](https://releases.llvm.org/), and [gcc-5](https://gcc.gnu.org/gcc-5/).

Optional: The garbage collector library [libgc.a](https://github.com/ivmai/bdwgc/). Need to install libgc.a in ssc/lib/.

Commands in ssc/bin/:

| command   | explanation                   |
|-----------|-------------------------------|
| ssc       | the SSC compiler using llc    |
| ssi       | the SSC interpreter using lli |
| ssc-shell | the SSC REPL interpreter      |

Examples in `ssc/tests`:

Use `ssc list.ssc` to compile `list.ssc` to `a.out`.
