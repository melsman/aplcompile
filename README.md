## aplcompile: An APL Compiler in Standard ML

This software implements an APL compiler in Standard ML. 

See [the compilation scheme](aplcompile/blob/master/comp.md).

## An example

Here is the result of compiling and running the following program:

```apl
signal ← {5+⍵}
+/ signal ⍳ 30
```

Here is what happens when the program is compiled and executed:

    mael@gaffy:~/gits/aplcompile$ ./test test.apl 
    Reading file: test.apl
    Program lexed:
     Id(signal) Larrow Lbra 5 Add Omega Rbra Newline Add Slash Id(signal) Iota 30 Newline Newline
    Parsing tokens...
    AST is
     [Assign(signal,Lam(Unres[5,Add,Omega])),Unres[Add,Slash,signal,Iota,30]]
    Resolving:
     Assign(signal,Lam(Unres[5,Add,Omega]))
    Resolving:
     Unres[Add,Slash,signal,Iota,30]
    Parse success:
     [Assign(signal,Lam(App2(Add,5,Omega))),App1(Opr1(Slash,Add),App1(signal,App1(Iota,30)))]
    Evaluating
    int kernel(int n1) {
      int n0 = 0;
      for (int n5 = 0; n5 < 30; n5++) {
	n0 = ((6+n0)+n5);
      }
      return n0;
    }
    Result is 615

## Try it!

The software makes use of the [smlunicode
library](https://github.com/melsman/smlunicode) project for lexing and
the [aplparse](https://github.com/melsman/aplparse) project for
parsing, which means that you need to checkout the
[smlunicode](https://github.com/melsman/smlunicode) sources and the
[aplparse](https://github.com/melsman/aplparse) sources in folders
next to the `aplcompile` sources.

You also need a Standard ML compiler (e.g., [Mlton](http://www.mlton.org/)).

Then simply write `make test` followed by `./test` in your shell.

## Limitations

Todo: Operators and improved error handling.

## License

This software is published under the [MIT License](MIT_LICENSE.md).
