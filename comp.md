## Compiling APL

Dynamically typed __terms__:

```sml
  type mi = Int Num m   (* Multidimensional integer array *)

  datatype s =          (* Terms *)
      Is of INT         (*   integer *)
    | Ds of DOUBLE      (*   double *)
    | Ais of mi         (*   integer array *)
    | Fs of s -> s M    (*   function in-lining *)
```

Environments (G) map identifiers (variables and symbols) to terms:

    G \in ENV = ID -> s

Compilation:

    [ _ ] _ _ : AST -> ENV -> (s * ENV -> s M) -> s M

    [e1; e2] G k =
      [e1] G (fn (s1,G1) =>
      [e2] (G1@G) (fn (s2,G2) =>
      k (s2,G2@G1)))

    [e1 + e2] G k =
      [e2] G (fn (s2,G2) =>
      [e1] (G2@G) (fn (s1,G1) =>
      case (s1, s2) of
           (Is i1, Is i2) => k(Is(i1+i2),G2@G1)
         | (Ais a1, Ais a2) => sum (op +) a1 a2 >>= (fn x => k(Ais x,G2@G1))
         | (Ais a1, Is i2) => k(Ais(mmap(fn x => x+i2)a1),G2@G1)
         | (Is i1, Ais a2) => k(Ais(mmap(fn x => i1+x)a2),G2@G1)
         | _ => err))

    [v <- e] G k =
       [e] G (fn (s,_) => k(s,{v->s}))

    [a] G k = k (G(a),{})

    [lam e] G k =
      let f x =
        let G' = {w -> x}
        in [e] (G'@G) (fn (s,_) => ret s)
      in k(Fs f,{})
      end

    [a(e)] G k =
      case G(a) of
         Fs f =>
           [e] G (fn (s,G') =>
           f s >>= (fn s' => k(s',G')))
       | _ => err

