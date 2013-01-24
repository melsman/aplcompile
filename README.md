## aplcompile: An APL Compiler in Standard ML

This software implements an APL compiler in Standard ML. 

See [the compilation scheme](aplcompile/blob/master/comp.md).

See also the [coverage page](aplcompile/blob/master/coverage.md).

## An example

Here is the result of compiling and running the following program:

```apl
signal ← {5+⍵}
+/ signal ⍳ 30
```

Here is what happens when the program is compiled and executed:

    mael@gaffy:~/gits/aplcompile$ ./aplc tests/test.apl 
    Reading file: tests/test.apl
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

## Another example

Here is the result of compiling the following program:

```apl
diff ← {1↓⍵−¯1⌽⍵}
signal ← {¯50⌈50⌊50×(diff 0,⍵)÷0.01+⍵}
+/ signal ⍳ 100
```
    mael@gaffy:~/gits/aplcompile$ ./aplc tests/signal.apl 
    Reading file: tests/signal.apl
    Parse success:
     [Assign(diff,Lam[0,1](App2(Drop,1,App2(Sub,Omega,App2(Rot,-1,Omega))))),Assign(signal,Lam[0,1](App2(Max,-50,App2(Min,50,App2(Times,50,App2(Div,App1(diff,App2(Cat,0,Omega)),App2(Add,0.01,Omega))))))),App1(AppOpr1[1](Slash,Add),App1(signal,App1(Iota,100)))]
    Evaluating
    double kernel(int n3) {
      double n2 = 0.0;
      for (int n7 = 0; n7 < 100; n7++) {
        n2 = (max(-50.0,min(50.0,(50.0*(i2d(((1+n7)-((n7<1) ? 0 : n7)))/(0.01+i2d((1+n7)))))))+n2);
      }
      return n2;
    }
    Result is 258.557340366

## Try it!

The software makes use of the [smlunicode
library](https://github.com/melsman/smlunicode) project for lexing,
the [aplparse](https://github.com/melsman/aplparse) project for
parsing, and the [MoA](https://github.com/melsman/MoA) project for implementing 
the fundamental APL array operations. This means that you need to checkout the
[smlunicode](https://github.com/melsman/smlunicode) sources, the
[aplparse](https://github.com/melsman/aplparse) sources, and the
[MoA](https://github.com/melsman/MoA) sources in folders
next to the `aplcompile` sources.

You also need a Standard ML compiler (e.g., [Mlton](http://www.mlton.org/)).

Then simply write `make aplc` followed by `./aplc` in your shell.

To run a series of tests, execute `make tests` in your shell.

## Limitations

Todo: Operators and improved error handling.

See also the [coverage page](aplcompile/blob/master/coverage.md).

## License

This software is published under the [MIT License](MIT_LICENSE.md).
