## Compiling APL

Two kinds of data:

```sml
  datatype D =
      A of m M       (* m: MoA array *)
    | F of m -> m M
```

Environments map variables (x) to data:

    E \in ENV = VAR -fin-> D

Compilation:

    [_]_ : EXP -> ENV -> D * ENV

    [a <- e; s] E =
      let (d, _) = [e]E
          E' = {a -> d}
      in [s](E'@E)

    [lam e] E =
      let f x =
        let E' = {w -> A(ret x)}
            (A m,_) = [e](E'@E)
        in m
      in (F f, emp)
      end

    [e1 + e2] E =
      let (A c2,E2) = [e2]E
          (A c1,E1) = [e1](E1@E)
      in (A(do m2 <- c2
               m1 <- c1
               ret m1+m2),
          E2@E1)
      end

    [a] E =
      (E(a),emp)

    [a(e)] E =
      let (A c,_) = [e]E
           F f = E(a)
      in (A(f(c)),emp)
