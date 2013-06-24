## aplcompile: An APL Compiler in Standard ML

This software implements an APL compiler in Standard ML. 

See [the compilation scheme](comp.md).

See also the [coverage page](coverage.md).

## An example

Here is the result of compiling and running the following program:

```apl
f ← {5+⍵}    ⍝ Function adding 5 to its argument (⍵)
+/ f ⍳ 30    ⍝ Apply f to the vector 1..30 and
             ⍝  sum up the elements in the resulting vector
```

Here is what happens when the program is compiled and executed:

    bash-3.2$ ./aplc tests/test.apl 
    Reading file: tests/test.apl
    Parse success:
     [Assign(f,Lam[0,1](App2(Add,5,Omega))),App1(AppOpr1[1](Slash,Add),App1(f,App1(Iota,30)))]
    Evaluating
    double kernel(int n1) {
      int n0 = 0;
      for (int n9 = 0; n9 < 30; n9++) {
	n0 = ((6+n0)+n9);
      }
      return i2d(n0);
    }
    Result is 615.0

## Another example

Consider the program

```apl
diff ← {1↓⍵−¯1⌽⍵}
signal ← {¯50⌈50⌊50×(diff 0,⍵)÷0.01+⍵}
+/ signal ⍳ 100
```

Here is the result of compiling it:

    bash-3.2$ ./aplc tests/signal.apl 
    Reading file: tests/signal.apl
    Parse success:
     [Assign(diff,Lam[0,1](App2(Drop,1,App2(Sub,Omega,App2(Rot,-1,Omega))))),
      Assign(signal,Lam[0,1](App2(Max,-50,App2(Min,50,App2(Times,50,App2(Div,App1(diff,App2(Cat,0,Omega)),App2(Add,0.01,Omega))))))),
      App1(AppOpr1[1](Slash,Add),App1(signal,App1(Iota,100)))]
    Evaluating
    double kernel(int n11) {
      double d10 = 0.0;
      for (int n59 = 0; n59 < 100; n59++) {
	d10 = (max(-50.0,min(50.0,(50.0*(i2d(((1+n59)-((n59<1) ? 0 : n59)))
	      / (0.01+i2d((1+n59)))))))+d10);
      }
      return d10;
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

Todo: Improved error handling.

See also the [coverage page](coverage.md).

## License

This software is published under the [MIT License](MIT_LICENSE.md).
