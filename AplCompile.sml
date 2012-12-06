structure AplCompile = struct

fun prln s = print(s ^ "\n")

fun minInt() = case Int.minInt of
                 SOME i => i
               | NONE => raise Fail "no minInt"
fun maxInt() = case Int.maxInt of
                 SOME i => i
               | NONE => raise Fail "no maxInt"

local
  open ILmoa

  type mi = Int Num m      (* Multidimensional integer array *)
  type md = Double Num m   (* Multidimensional double array *)

  datatype s =             (* Terms *)
      Is of INT            (*   integer *)
    | Ds of DOUBLE         (*   double *)
    | Ais of mi            (*   integer array *)
    | Ads of md            (*   double array *)
    | Fs of s list -> s M  (*   function in-lining *)

  open AplAst
  type env = (id * s) list
  fun lookup (E:env) id =
      case List.find (fn (id',_) => id = id') E of
        SOME(_,r) => SOME r
      | NONE => NONE
  val emp : env = []
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

datatype 'a identity_item = Lii of 'a
                          | Rii of 'a
                          | LRii of 'a
                          | NOii

type id_item = int identity_item * real identity_item * bool identity_item

fun id_item ii =
    case ii of
      Lii v => v
    | Rii v => v
    | LRii v => v
    | NOii => raise Fail "id_item: no identity item for function"

fun compOpr2_i8a2a opr1 opr2 =
 fn (Is i1, Ais a2) => ret(Ais(opr1 i1 a2))
  | (Is i1, Ads a2) => ret(Ads(opr2 i1 a2))
  | _ => raise Fail "compOpr2_i8a2a: expecting integer and array arguments"

fun compOpr2_a8a2aM opr1 opr2 =
 fn (Ais a1, Ais a2) => opr1 a1 a2 >>= (fn a => ret(Ais a))
  | (Ads a1, Ads a2) => opr2 a1 a2 >>= (fn a => ret(Ads a))
  | (Ais a1, e2) => compOpr2_a8a2aM opr1 opr2 (Ads(mmap i2d a1),e2)
  | (e1, Ais a2) => compOpr2_a8a2aM opr1 opr2 (e1,Ads(mmap i2d a2))
  | (Is i1,e2) => compOpr2_a8a2aM opr1 opr2 (Ais(scl i1),e2)
  | (e1, Is i2) => compOpr2_a8a2aM opr1 opr2 (e1,Ais(scl i2))
  | _ => raise Fail "compOpr2_a8a2aM: expecting two similar arrays as arguments"

fun compOpr2 opr oprd =
 fn (Is i1, Is i2) => ret(Is(opr(i1,i2)))
  | (Ds d1, Ds d2) => ret(Ds(oprd(d1,d2)))
  | (Ais a1, Ais a2) => sum Int opr a1 a2 >>= (fn x => ret(Ais x))
  | (Ads a1, Ads a2) => sum Double oprd a1 a2 >>= (fn x => ret(Ads x))
  | (Ais a1, Is i2) => ret(Ais(mmap(fn x => opr(x,i2))a1))
  | (Ads a1, Ds d2) => ret(Ads(mmap(fn x => oprd(x,d2))a1))
  | (Is i1, Ais a2) => ret(Ais(mmap(fn x => opr(i1,x))a2))
  | (Ds d1, Ads a2) => ret(Ads(mmap(fn x => oprd(d1,x))a2))
  | (Is i1, e2) => compOpr2 opr oprd (Ds(i2d i1),e2)
  | (e1, Is i2) => compOpr2 opr oprd (e1,Ds(i2d i2))
  | (Ais a1, e2) => compOpr2 opr oprd (Ads(mmap i2d a1),e2)
  | (e1, Ais a2) => compOpr2 opr oprd (e1,Ads(mmap i2d a2))
  | (Fs _,_) => raise Fail "compOpr2.function1"
  | (_, Fs _) => raise Fail "compOpr2.function2"

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
              k(Fs (fn [x] => compLam1 G e x
                     | [x,y] => compLam2 G e (x,y)
                     | l => raise Fail ("comp.LambE: expecting one or two arguments to be passed to lambda: " ^ Int.toString(List.length l))),
                emp)
            | IdE(Var v) => compId G (Var v) k
            | IdE(Symb L.Omega) => compId G (Symb L.Omega) k
            | IdE(Symb L.Alpha) => compId G (Symb L.Alpha) k
            | IdE(Symb L.Zilde) => k (Ais (zilde Int),emp)
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
            | App1E(e0,e1) =>
              let val f = compFun1 G e0
              in comp G e1 (fn (s,G') =>
                 f s >>= (fn s' => k(s',G')))
              end
            | App2E(e0,e1,e2) =>
              let val (f,_) = compFun2 G e0
              in comp G e2 (fn (s2,G2) =>
                 comp (G++G2) e1 (fn (s1,G1) =>
                 f(s1,s2) >>= (fn s' => k(s',G2++G1))))
              end
            | e => raise Fail ("compile.expression " ^ pr_exp e ^ " not implemented")
        and compLam1 G e x =
               let val G' = [(Symb L.Omega,x)]
               in comp (G++G') e (fn (s,_) => ret s)
               end
        and compLam2 G e (x,y) =
               let val G' = [(Symb L.Omega,y),(Symb L.Alpha,x)]
               in comp (G++G') e (fn (s,_) => ret s)
               end
        and compFun0 G e0 = raise Fail "comp: compFun0 not implemented"
        and compFun1 G e0 =
            case e0 of
              IdE(Var v) =>
              (case lookup G (Var v) of
                 SOME (Fs f) => (fn s => f [s])
               | SOME _ => raise Fail ("comp: variable " ^ v ^ " is not a function")
               | NONE => raise Fail ("comp: no variable " ^ v ^ " in the environment"))
            | IdE(Symb L.Iota) =>
              (fn Is i => ret(Ais(iota i))
                | _ => raise Fail "compFun1: iota expects integer argument")
            | LambE e1 => compLam1 G e1
            | App1E(IdE(Symb L.Slash),f) =>
              let val (f,ii) = compFun2 G f
              in (fn Ais x => red (fn (x,y) =>
                                      f(Is x,Is y) >>= (fn Is z => ret z
                                                         | _ => raise Fail "Opr1E"))
                                  (I(id_item(#1 ii))) x >>= (fn v => ret(Is v))
                   | Ads x => red (fn (x,y) =>
                                      f(Ds x,Ds y) >>= (fn Ds z => ret z
                                                         | _ => raise Fail "Opr1E"))
                                  (D(id_item(#2 ii))) x >>= (fn v => ret(Ds v))
                   | _ => raise Fail "comp.LambE: expecting one or two arguments to be passed to lambda")
              end
            | _ => raise Fail ("compFun1: expression not supported: " ^ pr_exp e0)
        and compFun2 G e0 =
            let val noii = (NOii,NOii,NOii)  (* see page 777 in Legrand, 1st Edition 2009, Mastering Dyalog APL *)
            in case e0 of
                 IdE(Var v) =>
                 (case lookup G (Var v) of
                    SOME (Fs f) => (fn (s1,s2) => f [s1,s2], noii)
                  | SOME _ => raise Fail ("comp: variable " ^ v ^ " is not a function")
                  | NONE => raise Fail ("comp: no variable " ^ v ^ " in the environment"))
               | IdE(Symb L.Take) => (compOpr2_i8a2a APL.take APL.take, noii)
               | IdE(Symb L.Drop) => (compOpr2_i8a2a APL.drop APL.drop, noii)
               | IdE(Symb L.Rot) => (compOpr2_i8a2a APL.rotate APL.rotate, noii)
               | IdE(Symb L.Cat) => (compOpr2_a8a2aM catenate catenate, noii)
               | IdE(Symb L.Add) => (compOpr2 (op +) (op +), (LRii 0, LRii 0.0, NOii))
               | IdE(Symb L.Sub) => (compOpr2 (op -) (op -), (Rii 0, Rii 0.0, NOii))
               | IdE(Symb L.Times) => (compOpr2 (op *) (op *), (LRii 1, LRii 1.0, NOii))
               | IdE(Symb L.Div) => (compOpr2 (op /) (op /), (Rii 1, Rii 1.0, NOii))
               | IdE(Symb L.Max) => (compOpr2 (uncurry max) (uncurry max), (LRii(minInt()), LRii Real.negInf, NOii))
               | IdE(Symb L.Min) => (compOpr2 (uncurry min) (uncurry min), (LRii(maxInt()), LRii Real.posInf, NOii))
               | LambE e1 => (compLam2 G e1, noii)
               | _ => raise Fail ("compFun2: expression not supported: " ^ pr_exp e0)            
            end
        and compId G id k =
            case lookup G id of
              SOME x => k(x,emp)
            | NONE => raise Fail ("compId: id " ^ AplAst.pr_id id ^ " not in environment")
        val c = comp emp e (fn (s,_) => ret s)
        val c' = 
            c >>= (fn s =>
                      case s of
                        Ais im => red (ret o op +) (I 0) im >>= (fn x => ret (i2d x))
                      | Is i => ret (i2d i)
                      | Ds d => ret d
                      | _ => raise Fail "expecting array")
    in runM Type.Double c'
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
