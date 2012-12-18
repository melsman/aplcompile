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

  datatype 'a identity_item = Lii of 'a
                            | Rii of 'a
                            | LRii of 'a
                            | NOii

  type id_item = int identity_item * real identity_item * bool identity_item
                 
  fun id_item ii v =
      case ii of
        Lii v => v
      | Rii v => v
      | LRii v => v
      | NOii => v
  val noii : id_item = (NOii,NOii,NOii)
  fun id_item_int ii = id_item (#1 ii) 0
  fun id_item_double ii = id_item (#2 ii) 0.0

  type mi = Int Num m       (* Multidimensional integer array *)
  type md = Double Num m    (* Multidimensional double array *)

  infix >>=

  datatype 'a N = S of 'a
                | M of 'a M
  infix >>>=
  val rett : 'a -> 'a N = fn a => S a
  fun (a: 'a N) >>>= (b: 'a -> 'b N) : 'b N =
      case a of
        M a => M(a >>= (fn a => case b a of S x => ret x
                                          | M m => m))
      | S a => b a 
  fun subM (M c) = c
    | subM (S e) = ret e

  datatype ty = Ity | Dty | Bty | Aty of ty | FUNty of ty list -> ty | APPty of ty list * ty 

  datatype s =                         (* Terms *)
      Is of INT                        (*   integer *)
    | Ds of DOUBLE                     (*   double *)
    | Ais of mi                        (*   integer array *)
    | Ads of md                        (*   double array *)
    | Fs of (s list -> s N) * id_item  (*   function in-lining *)

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
  fun repair s = String.translate (fn #"-" => "~"
                                    | c => String.str c) s
  fun StoI s = Int.fromString(repair s)
  fun StoD s = Real.fromString(repair s)
in

fun compOpr2_i8a2a opr1 opr2 =
 fn (Is i1, Ais a2) => S(Ais(opr1 i1 a2))
  | (Is i1, Ads a2) => S(Ads(opr2 i1 a2))
  | _ => raise Fail "compOpr2_i8a2a: expecting integer and array arguments"

fun compOpr2_a8a2aM opr1 opr2 =
 fn (Ais a1, Ais a2) => M(opr1 a1 a2 >>= (fn a => ret(Ais a)))
  | (Ads a1, Ads a2) => M(opr2 a1 a2 >>= (fn a => ret(Ads a)))
  | (Is i1,e2) => compOpr2_a8a2aM opr1 opr2 (Ais(scl i1),e2)
  | (e1, Is i2) => compOpr2_a8a2aM opr1 opr2 (e1,Ais(scl i2))
  | (Ds d1,e2) => compOpr2_a8a2aM opr1 opr2 (Ads(scl d1),e2)
  | (e1, Ds d2) => compOpr2_a8a2aM opr1 opr2 (e1,Ads(scl d2))
  | (Ais a1, e2) => compOpr2_a8a2aM opr1 opr2 (Ads(mmap i2d a1),e2)
  | (e1, Ais a2) => compOpr2_a8a2aM opr1 opr2 (e1,Ads(mmap i2d a2))
  | _ => raise Fail "compOpr2_a8a2aM: expecting two similar arrays as arguments"

fun compOpr2 opr oprd =
 fn (Is i1, Is i2) => S(Is(opr(i1,i2)))
  | (Ds d1, Ds d2) => S(Ds(oprd(d1,d2)))
  | (Ais a1, Ais a2) => M(sum Int opr a1 a2 >>= (fn x => ret(Ais x)))
  | (Ads a1, Ads a2) => M(sum Double oprd a1 a2 >>= (fn x => ret(Ads x)))
  | (Ais a1, Is i2) => S(Ais(mmap(fn x => opr(x,i2))a1))
  | (Ads a1, Ds d2) => S(Ads(mmap(fn x => oprd(x,d2))a1))
  | (Is i1, Ais a2) => S(Ais(mmap(fn x => opr(i1,x))a2))
  | (Ds d1, Ads a2) => S(Ads(mmap(fn x => oprd(d1,x))a2))
  | (Is i1, e2) => compOpr2 opr oprd (Ds(i2d i1),e2)
  | (e1, Is i2) => compOpr2 opr oprd (e1,Ds(i2d i2))
  | (Ais a1, e2) => compOpr2 opr oprd (Ads(mmap i2d a1),e2)
  | (e1, Ais a2) => compOpr2 opr oprd (e1,Ads(mmap i2d a2))
  | _ => raise Fail "compOpr2.function"

fun compOpr1 opr oprd =
 fn Is i => S(Is(opr i))
  | Ds d => S(Ds(oprd d))
  | Ais a => S(Ais(mmap opr a))
  | Ads a => S(Ads(mmap oprd a))
  | _ => raise Fail "compOpr1.function"

fun compOpr1d opr =
 fn Is i => S(Ds(opr(i2d i)))
  | Ds d => S(Ds(opr d))
  | Ais a => S(Ads(mmap (opr o i2d) a))
  | Ads a => S(Ads(mmap opr a))
  | _ => raise Fail "compOpr1d.function"

fun compOpr1i opr oprd =
 fn Is i => S(Is(opr i))
  | Ds d => S(Is(oprd d))
  | Ais a => S(Ais(mmap opr a))
  | Ads a => S(Ais(mmap oprd a))
  | _ => raise Fail "compOpr1i.function"

fun signi x = If(x < I 0,I ~1, I 1)
fun signd x = If(x < D 0.0,I ~1, I 1)

fun compileAst e =
    let fun comp (G:env) e (k: s*env -> s N) : s N =
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
            | LambE((1,1),e) => (* monadic operator => monadic function *)
              k(Fs (fn [f] => compLam11 G e f
                     | _ => raise Fail "comp.LambE(1,1): expecting 1 operator argument",
                    noii),
                emp)
            | LambE((1,2),e) => (* monadic operator => dyadic function *)
              k(Fs (fn [f] => compLam12 G e f
                     | _ => raise Fail "comp.LambE(1,2): expecting 1 operator argument",
                    noii),
                emp)
            | LambE((0,1),e) =>
              k(Fs (fn [x] => compLam01 G e x
                     | l => raise Fail ("comp.LambE(0,1): expecting one argument to be passed to lambda: " ^ Int.toString(List.length l)),
                    noii),
                emp)
            | LambE((0,2),e) =>
              k(Fs (fn [x,y] => compLam02 G e (x,y)
                     | l => raise Fail ("comp.LambE(0,2): expecting two arguments to be passed to lambda: " ^ Int.toString(List.length l)),
                    noii),
                emp)
            | LambE((x,y),e) =>
              raise Fail ("comp.LambE: case not supported: (" ^ Int.toString x ^ "," ^ Int.toString y ^ ")")
            | IdE(Var v) => compId G (Var v) k
            | IdE(Symb L.Omega) => compId G (Symb L.Omega) k
            | IdE(Symb L.Omegaomega) => compId G (Symb L.Omegaomega) k
            | IdE(Symb L.Alpha) => compId G (Symb L.Alpha) k
            | IdE(Symb L.Alphaalpha) => compId G (Symb L.Alphaalpha) k
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
              comp G e1 (fn (s,G') =>
              comp (G++G') e0 (fn (f,G'') =>
                                  case f of
                                    Fs (f,_) => f [s] >>>= (fn s' => k(s',G'++G''))
                                  | _ => raise Fail "comp.App1E: expecting function"))
            | App2E(e0,e1,e2) =>
              comp G e2 (fn (s2,G2) =>
              comp (G++G2) e0 (fn (f,G0) =>
              comp (G++G2++G0) e1 (fn (s1,G1) =>
                                      case f of
                                        Fs (f,_) => f[s1,s2] >>>= (fn s' => k(s',G2++G0++G1))
                                      | _ => raise Fail "comp.App2E: expecting function")))
            | AppOpr1E(_,e0,e1) =>
              comp G e1 (fn (s,G') =>
              comp (G++G') e0 (fn (f,G'') =>
                                  case f of
                                    Fs (f,_) => f [s] >>>= (fn s' => k(s',G'++G''))
                                  | _ => raise Fail "comp.AppOpr1E: expecting operator as function"))
            | IdE(Symb L.Slash) => 
              k(Fs (fn [Fs (f,ii)] =>
                       rett(Fs (fn [Ais x] => M(APL.reduce (fn (x,y) =>
                                                        subM(f[Is x,Is y] >>>= (fn Is z => rett z
                                                                                 | _ => raise Fail "comp.Slash: expecting integer as result")))
                                                    (I(id_item_int ii)) x Is Ais)
                                 | [Ads x] => M(APL.reduce (fn (x,y) =>
                                                        subM(f[Ds x,Ds y] >>>= (fn Ds z => rett z
                                                                                 | _ => raise Fail "comp.Slash: expecting double as result")))
                                                    (D(id_item_double ii)) x Ds Ads)
                                 | [Ds x] => S(Ds x)
                                 | [Is x] => S(Is x)
                                 | _ => raise Fail "comp.Slash: expecting array",
                                noii))
                     | _ => raise Fail "comp.Slash: expecting function as operator argument",
                    noii), 
                emp)
            | IdE(Symb L.Each) => 
              k(Fs (fn [Fs (f,_)] =>
                       let exception No
                           fun tryInt g x =
                               mmap (fn x => case f[g x] of S(Is v) => v
                                                           | _ => raise No) x
                           fun tryDouble g x =
                               mmap (fn x => case f[g x] of S(Ds v) => v
                                                          | _ => raise Fail "Not Ds") x
                       in rett(Fs (fn [Ais x] => (S(Ais(tryInt Is x)) handle No => S(Ads(tryDouble Is x)))
                                    | [Ads x] => (S(Ais(tryInt Ds x)) handle No => S(Ads(tryDouble Ds x)))
                                    | _ => raise Fail "comp.Each: expecting array",
                                   noii))
                       end
                     | _ => raise Fail "comp.Each: expecting function as operator argument",
                    noii), 
                emp)
            | IdE(Symb L.Iota) => compPrimFunM k (fn Is i => S(Ais(iota i))
                                                   | _ => raise Fail "comp.Iota: expecting integer argument")
            | IdE(Symb L.Trans) => compPrimFunM k (fn Ais a => S(Ais(APL.trans a))
                                                    | Ads a => S(Ads(APL.trans a))
                                                    | _ => raise Fail "comp.Trans: expecting array")
            | IdE(Symb L.Rho) => compPrimFunMD k (fn Ais a => S(Ais(APL.shape a))
                                                   | Ads a => S(Ais(APL.shape a))
                                                   | _ => raise Fail "comp.Rho.shape expects an array",
                                                  fn (Ais a1, Ais a2) => M(APL.reshape a1 a2) >>>= (fn a => rett(Ais a))
                                                   | (Ais a1, Ads a2) => M(APL.reshape a1 a2) >>>= (fn a => rett(Ads a))
                                                   | _ => raise Fail "comp.Rho.reshape expects arrays") noii
            | IdE(Symb L.Cat) => compPrimFunMD k (fn Ais a => S(Ais(rav a))
                                                   | Ads a => S(Ads(rav a))
                                                   | _ => raise Fail "comp.Cat.rav expects an array",
                                                  compOpr2_a8a2aM catenate catenate) noii
            | IdE(Symb L.Take) => compPrimFunD k (compOpr2_i8a2a APL.take APL.take) noii
            | IdE(Symb L.Drop) => compPrimFunD k (compOpr2_i8a2a APL.drop APL.drop) noii
            | IdE(Symb L.Rot) => compPrimFunD k (compOpr2_i8a2a APL.rotate APL.rotate) noii
            | IdE(Symb L.Add) => compPrimFunMD k (S,
                                                  compOpr2 (op +) (op +)) noii
            | IdE(Symb L.Sub) => compPrimFunMD k (compOpr1 ~ ~,
                                                  compOpr2 (op -) (op -)) noii
            | IdE(Symb L.Times) => compPrimFunMD k (compOpr1i signi signd,
                                                    compOpr2 (op * ) (op * )) (LRii 1,LRii 1.0,NOii)
            | IdE(Symb L.Div) => compPrimFunMD k (compOpr1d (fn x => D 1.0 / x),
                                                  compOpr2 (op /) (op /)) (LRii 1,LRii 1.0,NOii)
            | IdE(Symb L.Max) => compPrimFunD k (compOpr2 (uncurry max) (uncurry max)) (LRii(minInt()), LRii(Real.negInf), NOii)
            | IdE(Symb L.Min) => compPrimFunD k (compOpr2 (uncurry min) (uncurry min)) (LRii(maxInt()), LRii(Real.posInf),NOii)
            | e => raise Fail ("compile.expression " ^ pr_exp e ^ " not implemented")
        and compPrimFunMD k (mon,dya) ii =
            k(Fs (fn [x1,x2] => dya (x1,x2)
                   | [x] => mon x
                   | _ => raise Fail "compPrimFun: expecting one or two arguments",
                  ii),
              emp)
        and compPrimFunM k mon =
            k(Fs (fn [x] => mon x
                   | _ => raise Fail "compPrimFunM: expecting one argument",
                  noii),
              emp) 
        and compPrimFunD k dya ii =
            k(Fs (fn [x1,x2] => dya (x1,x2)
                   | _ => raise Fail "compPrimFunD: expecting two arguments",
                  ii),
              emp)
           
        and compId G id k =
            case lookup G id of
              SOME x => k(x,emp)
            | NONE => raise Fail ("compId: id " ^ AplAst.pr_id id ^ " not in environment")
        and compLam11 G e f =
            rett(Fs(fn [x] =>
                       let val G' = [(Symb L.Alphaalpha, f),(Symb L.Omega, x)]
                       in comp (G++G') e (fn (s,_) => rett s)
                       end
                     | _ => raise Fail "compLam11: expecting 1 argument",
                    noii))
        and compLam12 G e f =
            rett(Fs(fn [x,y] =>
                       let val G' = [(Symb L.Alphaalpha, f),(Symb L.Omega, x),(Symb L.Alpha, y)]
                       in comp (G++G') e (fn (s,_) => rett s)
                       end
                     | _ => raise Fail "compLam12: expecting 2 arguments",
                    noii))
        and compLam01 G e x =
            let val G' = [(Symb L.Omega,x)]
            in comp (G++G') e (fn (s,_) => rett s)
            end
        and compLam02 G e (x,y) =
            let val G' = [(Symb L.Omega,y),(Symb L.Alpha,x)]
            in comp (G++G') e (fn (s,_) => rett s)
            end
        val c = comp emp e (fn (s,_) => rett s)
        val c' = subM c >>= (fn s =>
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
