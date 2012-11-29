structure AplCompile = struct

fun prln s = print(s ^ "\n")

local
  open ILmoa

  type mi = Int Num m    (* Multidimensional integer array *)
  type md = Double Num m (* Multidimensional double array *)

  datatype s =           (* Terms *)
      Is of INT          (*   integer *)
    | Ds of DOUBLE       (*   double *)
    | Ais of mi          (*   integer array *)
    | Ads of md          (*   double array *)
    | Fs of s -> s M     (*   function in-lining *)

  open AplAst
  type env = (id * s) list
  fun lookup E id =
      case List.find (fn (id',_) => id = id) E of
        SOME(_,r) => SOME r
      | NONE => NONE
  val emp = []
  fun plus (e1,e2) = e2@e1
  infix ++ 
  val op ++ = plus
  fun uncurry f (x,y) = f x y
  infix >>=
  fun repair s = String.translate (fn #"-" => "~"
                                    | c => String.str c) s
  fun StoI s = Int.fromString(repair s)
  fun StoD s = Real.fromString(repair s)
in

fun compOpr2_i8a2a comp G e1 e2 opr1 opr2 k =
    comp G e2 (fn (s2,G2) =>
    comp (G++G2) e1 (fn (s1,G1) =>
    case (s1,s2) of
      (Is i1, Ais a2) => k(Ais(opr1 i1 a2),G2++G1)
    | (Is i1, Ads a2) => k(Ads(opr2 i1 a2),G2++G1)
    | _ => raise Fail "compOpr2_i8a2a: expecting integer and array arguments"))

fun compOpr2_a8a2aM comp G e1 e2 opr1 opr2 k =
    comp G e2 (fn (s2,G2) =>
    comp (G++G2) e1 (fn (s1,G1) =>
    case (s1,s2) of
      (Ais a1, Ais a2) => opr1 a1 a2 >>= (fn a => k(Ais a,G2++G1))
    | (Ads a1, Ads a2) => opr2 a1 a2 >>= (fn a => k(Ads a,G2++G1))
    | _ => raise Fail "compOpr2_a8a2aM: expecting two similar arrays as arguments"))

fun compileAst e =
    let fun comp G e k =
            case e of
              IntE s =>
              (case StoI s of
                 SOME i => k (Is(I i),emp)
               | NONE => raise Fail ("error parsing integer " ^ s))
            | DoubleE s =>
              (case StoD s of
                 SOME d => k (Ds(D d),emp)
               | NONE => raise Fail ("error parsing double " ^ s))
            | AssignE(v,e) => comp G e (fn (s,_) => k(s,[(Var v,s)]))
            | SeqE [] => raise Fail "comp: empty Seq"
            | SeqE [e] => comp G e k
            | SeqE (e1::es) =>
              comp G e1 (fn (s1,G1) =>
              comp (G++G1) (SeqE es) (fn (s2,G2) =>
              k(s2,G1++G2)))
            | LambE e =>
              let fun f x =
                      let val G' = [(Symb L.Omega,x)]
                      in comp (G++G') e (fn (s,_) => ret s)
                      end
              in k(Fs f,emp)
              end
            | VarE v => compId G (Var v) k
            | SymbE L.Omega => compId G (Symb L.Omega) k
            | VecE es =>
              (case List.foldr (fn (IntE s,SOME acc) =>
                                   (case StoI s of
                                      SOME i => SOME(I i::acc)
                                    | NONE => NONE)
                                 | _ => NONE) (SOME[]) es of
                 SOME is => k(Ais(vec(fromList is)),emp)
               | NONE =>
                 case List.foldr (fn (e,acc) =>
                                     let val s = case e of
                                                   IntE s => s
                                                 | DoubleE s => s
                                                 | _ => raise Fail "expecting only integers or doubles"
                                     in case StoD s of
                                          SOME d => D d :: acc
                                        | NONE => raise Fail ("could not parse double value " ^ s)
                                     end) [] es of
                   [] => raise Fail "expecting a non-empty sequence of integers or doubles"
                 | ds => k(Ads(vec(fromList ds)),emp))
            | App1E(Var v,e1) =>
              (case lookup G v of
                 SOME (Fs f) =>
                 comp G e1 (fn (s,G') =>
                 (f s) >>= (fn s' => k(s',G')))
               | SOME _ => raise Fail ("comp: variable " ^ v ^ " is not a function")
               | NONE => raise Fail ("comp: no variable " ^ v ^ " in the environment"))
            | App1E(Symb L.Iota,e1) => compOpr1_i2ia G e1 iota k
            | App2E(Symb L.Take,e1,e2) => compOpr2_i8a2a comp G e1 e2 APL.take APL.take k
            | App2E(Symb L.Drop,e1,e2) => compOpr2_i8a2a comp G e1 e2 APL.drop APL.drop k
            | App2E(Symb L.Rot,e1,e2) => compOpr2_i8a2a comp G e1 e2 APL.rotate APL.rotate k
            | App2E(Symb L.Cat,e1,e2) => compOpr2_a8a2aM comp G e1 e2 catenate catenate k
            | App2E(Symb L.Add,e1,e2) => compOpr2 G e1 e2 (op +) k
            | App2E(Symb L.Sub,e1,e2) => compOpr2 G e1 e2 (op -) k
            | App2E(Symb L.Times,e1,e2) => compOpr2 G e1 e2 (op *) k
            | App2E(Symb L.Div,e1,e2) => compOpr2 G e1 e2 (op /) k
            | App2E(Symb L.Max,e1,e2) => compOpr2 G e1 e2 (uncurry max) k
            | App2E(Symb L.Min,e1,e2) => compOpr2 G e1 e2 (uncurry min) k
            | e => raise Fail ("compile.expression " ^ pr_exp e ^ " not implemented")
        and compOpr1_i2ia G e1 opr k =
          comp G e1 (fn (s1,G1) =>
          case s1 of
            Is i1 => k(Ais(opr i1),G1)
          | _ => raise Fail "compOpr1_i2ia: expecting integer argument")
        and compOpr2 G e1 e2 opr k =
          comp G e2 (fn (s2,G2) =>
          comp (G++G2) e1 (fn (s1,G1) =>
          case (s1,s2) of
            (Is i1, Is i2) => k(Is(opr(i1,i2)),G2++G1)
          | (Ais a1, Ais a2) => sum Int opr a1 a2 >>= (fn x => k(Ais x,G2++G1))
          | (Ais a1, Is i2) => k(Ais(mmap(fn x => opr(x,i2))a1),G2++G1)
          | (Is i1, Ais a2) => k(Ais(mmap(fn x => opr(i1,x))a2),G2++G1)
          | (Ds _, _) => raise Fail "AppE2.double1"
          | (_, Ds _) => raise Fail "AppE2.double2"
          | (Ads _, _) => raise Fail "AppE2.double array1"
          | (_, Ads _) => raise Fail "AppE2.double array2"
          | (Fs _,_) => raise Fail "AppE2.function1"
          | (_, Fs _) => raise Fail "AppE2.function2"))
        and compId G id k =
            case lookup G id of
              SOME x => k(x,emp)
            | NONE => raise Fail ("compId: id " ^ AplAst.pr_id id ^ " not in environment")
        val c = comp emp e (fn (s,_) => ret s)
        val c' = 
            c >>= (fn s =>
                      case s of
                        Ais im => red (ret o op +) (I 0) im
                      | _ => raise Fail "expecting array")
    in runM Type.Int c'
    end
end

fun compileAndRun s =
    let val ts = AplLex.lex s
        val () = prln "Program lexed:"
        val () = prln (" " ^ AplLex.pr_tokens ts)
        val () = prln "Parsing tokens..."
    in case AplParse.parse AplParse.env0 ts of
         SOME (e,_) => 
         (prln("Parse success:\n " ^ AplAst.pr_exp e);
          let val p = compileAst e
              val () = prln("Evaluating")
              val v = ILmoa.eval p ILmoa.Uv
          in prln("Result is " ^ ILmoa.ppV v)
          end)
       | NONE => prln "Parse error."
    end

fun readFile f =
    let val is = TextIO.openIn f
    in let val s = TextIO.inputAll is
       in TextIO.closeIn is;
          s
       end handle ? => (TextIO.closeIn is; raise ?)
    end

fun compileAndRunFile f =
    let val () = prln ("Reading file: " ^ f)
        val c = readFile f
    in compileAndRun c
    end

end
