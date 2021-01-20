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

## Example demonstrating transpose and a double-reduce

Consider the following APL program:

```apl
a ← 3 2 ⍴ ⍳ 5
a2 ← 3 2 ⍴ ⍳ 4
b ← ⍉ a
c ← b, ⍉ a2
×/ +/ c

⍝ 1 2  1 3 5  -+-> 9
⍝ 3 4  2 4 1  -+-> 7
⍝ 5 1
⍝      1 3 1  -+-> 5
⍝      2 4 2  -+-> 8
⍝                 ---
⍝                 2520
```

Here is the result of compiling it:

    bash-3.2$ ./aplc tests/test15.apl
    Reading file: tests/test15.apl
    Parse success:
     [Assign(a,App2(Rho,Vec[3,2],App1(Iota,5))),
      Assign(a2,App2(Rho,Vec[3,2],App1(Iota,4))),
      Assign(b,App1(Trans,a)),
      Assign(c,App2(Cat,b,App1(Trans,a2))),
      App1(AppOpr1[1](Slash,Times),App1(AppOpr1[1](Slash,Add),c))]
    Evaluating
    double kernel(int n17) {
      int n16 = 1;
      for (int n89 = 0; n89 < 4; n89++) {
        int n39 = 0;
        for (int n92 = 0; n92 < min(3,max((12-(n89*3)),0)); n92++) {
          n39 = ((((n92+(n89*3))<6) ? (((((n92+(n89*3))==5) ? (n92+(n89*3)) :
                ((2*(n92+(n89*3)))%5))%5)+1) : ((((((n92+(n89*3))-6)==5) ? ((n92+(n89*3))-6) :
                ((2*((n92+(n89*3))-6))%5))%4)+1))+n39);
        }
        n16 = (n39*n16);
      }
      return i2d(n16);
    }
    Result is 2520.0

## Example demonstrating matrix-multiplication

```apl
a ← 3 2 ⍴ ⍳ 5
b ← ⍉ a
c ← a +.× b
×/ +/ c

⍝       1  3  5
⍝       2  4  1
⍝
⍝ 1 2   5 11  7  -+->    23
⍝ 3 4  11 25 19  -+->    55
⍝ 5 1   7 19 26  -+->    52
⍝                     65780
```

Here is the result of compiling the example:

    bash-3.2$ ./aplc tests/test13.apl
    Reading file: tests/test13.apl
    Parse success:
     [Assign(a,App2(Rho,Vec[3,2],App1(Iota,5))),
      Assign(b,App1(Trans,a)),
      Assign(c,App2(AppOpr2[2](Dot,Add,Times),a,b)),
      App1(AppOpr1[1](Slash,Times),App1(AppOpr1[1](Slash,Add),c))]
    Evaluating
    double kernel(int n8) {
      int n7 = 1;
      for (int n180 = 0; n180 < 3; n180++) {
        int n26 = 0;
        for (int n192 = 0; n192 < min(3,max((9-(n180*3)),0)); n192++) {
          int n53 = 0;
          for (int n195 = 0; n195 < min(min(2,max((6-(((n192+(n180*3))/3)*2)),0)),min(2,max((6-(((n192+(n180*3))%3)*2)),0))); n195++) {
            n53 = (((((n195+(((n192+(n180*3))/3)*2))%5)+1)*(((((((n195+(((n192+(n180*3))%3)*2))==5)
                  ? (n195+(((n192+(n180*3))%3)*2)) : ((3*(n195+(((n192+(n180*3))%3)*2)))%5))==5)
                  ? (((n195+(((n192+(n180*3))%3)*2))==5)
                  ? (n195+(((n192+(n180*3))%3)*2)) : ((3*(n195+(((n192+(n180*3))%3)*2)))%5))
                  : ((2*(((n195+(((n192+(n180*3))%3)*2))==5)
                  ? (n195+(((n192+(n180*3))%3)*2))
                  : ((3*(n195+(((n192+(n180*3))%3)*2)))%5)))%5))%5)+1))+n53);
          }
          n26 = (n53+n26);
        }
        n7 = (n26*n7);
      }
      return i2d(n7);
    }
    Result is 65780.0


## Try it!

The software makes use of the [sml-unicode
library](https://github.com/diku-dk/sml-unicode) project for lexing,
the [sml-aplparse](https://github.com/diku-dk/sml-aplparse) project for
parsing, and the [MoA](https://github.com/melsman/MoA) project for implementing
the fundamental APL array operations.

The sources are setup to work well with [smlpkg](https://github.com/diku-dk/smlpkg)

You need a Standard ML compiler (e.g., [Mlton](http://www.mlton.org/) or [MLKit](https://github.com/melsman/mlkit)).

Then simply write `make aplc` followed by `./aplc` in your shell.

To run a series of tests, execute `make tests` in your shell.

## Limitations

Todo: Improved error handling.

See also the [coverage page](coverage.md).

## License

This software is published under the [MIT License](MIT_LICENSE.md).
