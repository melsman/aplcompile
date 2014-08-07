functor AplCompile(X : ILAPL) :
sig
  type flag = string * string option  (* supported flags: [-o f, -c, -v] *)
  val compileAndRun     : flag list -> string -> unit
  val compileAndRunFile : flag list -> string -> unit
end = 
struct

type flag =  string * string option

fun prln s = print(s ^ "\n")

fun minInt() = case Int.minInt of
                 SOME i => i
               | NONE => raise Fail "no minInt"
fun maxInt() = case Int.maxInt of
                 SOME i => i
               | NONE => raise Fail "no maxInt"

local
  open X

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
  fun id_item_int (ii:id_item) = id_item (#1 ii) 0
  fun id_item_double (ii:id_item) = id_item (#2 ii) 0.0
  fun id_item_bool (ii:id_item) = id_item (#3 ii) false

  type mb = Bool m          (* Multidimensional bool array *)
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
      Bs of BOOL                       (*   boolean *)
    | Is of INT                        (*   integer *)
    | Ds of DOUBLE                     (*   double *)
    | Abs of mb                        (*   boolean array *)
    | Ais of mi                        (*   integer array *)
    | Ads of md                        (*   double array *)
    | Fs of (s list -> s N) * id_item  (*   function in-lining *)

  fun lets s = case s of
                   Bs _ => ret s
                 | Is _ => ret s
                 | Ds _ => ret s
                 | Abs mb => letm Bool mb >>= (fn x => ret(Abs x))
                 | Ais mi => letm Int mi >>= (fn x => ret(Ais x))
                 | Ads md => letm Double md >>= (fn x => ret(Ads x))
                 | Fs _ => ret s

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

fun b2i b = If(b, I 1, I 0)

fun compOpr2_i8a2a e opr1 opr2 opr3 =
 fn (Is i1, Ais a2) => S(Ais(opr1 i1 a2))
  | (Is i1, Ads a2) => S(Ads(opr2 i1 a2))
  | (Is i1, Abs a2) => S(Abs(opr3 i1 a2))
(*
  | (Ais a1, Ais a2) => S(Ais(opr1 (pick a1) a2))
  | (Ais a1, Ads a2) => S(Ads(opr2 (pick a1) a2))
*)
  | (Bs b1, e2) => compOpr2_i8a2a e opr1 opr2 opr3 (Is(b2i b1),e2)
  | _ => raise Fail ("compOpr2_i8a2a: expecting integer and array arguments in " ^ pr_exp e)

fun compOpr2_a8a2aM opr1 opr2 opr3 =
 fn (Ais a1, Ais a2) => M(opr1 a1 a2 >>= (fn a => ret(Ais a)))
  | (Ads a1, Ads a2) => M(opr2 a1 a2 >>= (fn a => ret(Ads a)))
  | (Abs a1, Abs a2) => M(opr3 a1 a2 >>= (fn a => ret(Abs a)))
  | (Is i1,e2) => compOpr2_a8a2aM opr1 opr2 opr3 (Ais(scl Int i1),e2)
  | (e1, Is i2) => compOpr2_a8a2aM opr1 opr2 opr3 (e1,Ais(scl Int i2))
  | (Ds d1,e2) => compOpr2_a8a2aM opr1 opr2 opr3 (Ads(scl Double d1),e2)
  | (e1, Ds d2) => compOpr2_a8a2aM opr1 opr2 opr3 (e1,Ads(scl Double d2))
  | (Bs b1,e2) => compOpr2_a8a2aM opr1 opr2 opr3 (Abs(scl Bool b1),e2)
  | (e1, Bs b2) => compOpr2_a8a2aM opr1 opr2 opr3 (e1,Abs(scl Bool b2))
  | (Abs a1, e2) => compOpr2_a8a2aM opr1 opr2 opr3 (Ais(each Bool Int (ret o b2i) a1),e2)
  | (e1, Abs a2) => compOpr2_a8a2aM opr1 opr2 opr3 (e1,Ais(each Bool Int (ret o b2i) a2))
  | (Ais a1, e2) => compOpr2_a8a2aM opr1 opr2 opr3 (Ads(each Int Double (ret o i2d) a1),e2)
  | (e1, Ais a2) => compOpr2_a8a2aM opr1 opr2 opr3 (e1,Ads(each Int Double (ret o i2d) a2))
  | _ => raise Fail "compOpr2_a8a2aM: expecting two similar arrays as arguments"

fun compOpr2 opi opd =
 fn (Is i1, Is i2) => S(Is(opi(i1,i2)))
  | (Ds d1, Ds d2) => S(Ds(opd(d1,d2)))
  | (Ais a1, Ais a2) => M(sum Int Int Int (ret o opi) a1 a2 >>= (fn x => ret(Ais x)))
  | (Ads a1, Ads a2) => M(sum Double Double Double (ret o opd) a1 a2 >>= (fn x => ret(Ads x)))
  | (Ais a1, Is i2) => S(Ais(each Int Int (fn x => ret(opi(x,i2)))a1))
  | (Ads a1, Ds d2) => S(Ads(each Double Double (fn x => ret(opd(x,d2)))a1))
  | (Is i1, Ais a2) => S(Ais(each Int Int (fn x => ret(opi(i1,x)))a2))
  | (Ds d1, Ads a2) => S(Ads(each Double Double (fn x => ret(opd(d1,x)))a2))
  | (Bs b1, e2) => compOpr2 opi opd (Is(b2i b1),e2)
  | (e1, Bs b2) => compOpr2 opi opd (e1,Is(b2i b2))
  | (Is i1, e2) => compOpr2 opi opd (Ds(i2d i1),e2)
  | (e1, Is i2) => compOpr2 opi opd (e1,Ds(i2d i2))
  | (Abs a1, e2) => compOpr2 opi opd (Ais(each Bool Int (ret o b2i) a1),e2)
  | (e1, Abs a2) => compOpr2 opi opd (e1,Ais(each Bool Int (ret o b2i) a2))
  | (Ais a1, e2) => compOpr2 opi opd (Ads(each Int Double (ret o i2d) a1),e2)
  | (e1, Ais a2) => compOpr2 opi opd (e1,Ads(each Int Double (ret o i2d) a2))
  | _ => raise Fail "compOpr2.function"

fun compCmp opi opd =
 fn (Is i1, Is i2) => S(Bs(opi(i1,i2)))
  | (Ds d1, Ds d2) => S(Bs(opd(d1,d2)))
  | (Ais a1, Ais a2) => M(sum Int Int Bool (ret o opi) a1 a2 >>= (fn x => ret(Abs x)))
  | (Ads a1, Ads a2) => M(sum Double Double Bool (ret o opd) a1 a2 >>= (fn x => ret(Abs x)))
  | (Ais a1, Is i2) => S(Abs(each Int Bool (fn x => ret(opi(x,i2)))a1))
  | (Ads a1, Ds d2) => S(Abs(each Double Bool (fn x => ret(opd(x,d2)))a1))
  | (Is i1, Ais a2) => S(Abs(each Int Bool (fn x => ret(opi(i1,x)))a2))
  | (Ds d1, Ads a2) => S(Abs(each Double Bool (fn x => ret(opd(d1,x)))a2))
  | (Is i1, e2) => compCmp opi opd (Ds(i2d i1),e2)
  | (e1, Is i2) => compCmp opi opd (e1,Ds(i2d i2))
  | (Ais a1, e2) => compCmp opi opd (Ads(each Int Double (ret o i2d) a1),e2)
  | (e1, Ais a2) => compCmp opi opd (e1,Ads(each Int Double (ret o i2d) a2))
  | _ => raise Fail "compCmp.function"

fun compOpr1 opi opd =
 fn Is i => S(Is(opi i))
  | Ds d => S(Ds(opd d))
  | Bs b => compOpr1 opi opd (Is(b2i b))
  | Ais a => S(Ais(each Int Int (ret o opi) a))
  | Ads a => S(Ads(each Double Double (ret o opd) a))
  | Abs a => compOpr1 opi opd (Ais(each Bool Int (ret o b2i) a))
  | _ => raise Fail "compOpr1.function"

fun compOpr1d opd =
 fn Is i => S(Ds(opd(i2d i)))
  | Ds d => S(Ds(opd d))
  | Bs b => compOpr1d opd (Is(b2i b))
  | Ais a => S(Ads(each Int Double (ret o opd o i2d) a))
  | Ads a => S(Ads(each Double Double (ret o opd) a))
  | Abs a => compOpr1d opd (Ais(each Bool Int (ret o b2i) a))
  | _ => raise Fail "compOpr1d.function"

fun compOpr1i opi opd =
 fn Is i => S(Is(opi i))
  | Ds d => S(Is(opd d))
  | Bs b => compOpr1i opi opd (Is(b2i b))
  | Ais a => S(Ais(each Int Int (ret o opi) a))
  | Ads a => S(Ais(each Double Int (ret o opd) a))
  | Abs a => compOpr1i opi opd (Ais(each Bool Int (ret o b2i) a))
  | _ => raise Fail "compOpr1i.function"

fun signi x = If(lti(x,I 0),I ~1, I 1)
fun signd x = If(ltd(x,D 0.0),I ~1, I 1)

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
            | AssignE(v,e) => 
              let fun cont f x = let val t = f x in k(t,[(Var v,t)]) end
              in comp G e (fn (Ais a,_) => M(letm_asgn Int a) >>>= cont Ais
                          | (Ads a,_) => M(letm_asgn Double a) >>>= cont Ads
                          | (Is a,_) => M(lett Int a) >>>= cont Is
                          | (Ds a,_) => M(lett Double a) >>>= cont Ds
                          | (s,_) => k(s,[(Var v,s)]))
              end
            | SeqE [] => raise Fail "comp: empty Seq"
            | SeqE [e] => comp G e k
            | SeqE (e1::es) =>
              comp G e1 (fn (s1,G1) =>
              comp (G++G1) (SeqE es) (fn (s2,G2) =>
              k(s2,G1++G2)))
            | LambE((2,2),e) => (* dyadic operator => dyadic function *)
              k(Fs (fn [f,g] => compLam22 G e (f,g)
                     | _ => raise Fail "comp.LambE(2,2): expecting 2 operator arguments",
                    noii),
                emp)
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
              k(Fs (fn [x] => M(lets x) >>>= compLam01 G e
                     | l => raise Fail ("comp.LambE(0,1): expecting one argument to be passed to lambda: " ^ Int.toString(List.length l)),
                    noii),
                emp)
            | LambE((0,2),e) =>
              k(Fs (fn [x,y] => compLam02 G e (x,y)
                     | l => raise Fail ("comp.LambE(0,2): expecting two arguments to be passed to lambda: " ^ Int.toString(List.length l)),
                    noii),
                emp)
            | LambE((0,0),e) => comp G (LambE((0,1),e)) k   (* support for constant functions *)
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
                 SOME is => (M(fromListM Int is)) >>>= (fn e => k(Ais(vec e),emp))
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
                 | ds => (M(fromListM Double ds)) >>>= (fn e => k(Ads(vec e),emp)))   (*k(Ads(vec(fromList Double ds)),emp))*)
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
                                  | _ => raise Fail "comp.AppOpr1E: expecting function"))
            | AppOpr2E(_,e0,e1,e2) =>
              comp G e2 (fn (s2,G2) =>
              comp (G++G2) e1 (fn (s1,G1) =>
              comp (G++G2++G1) e0 (fn (f,G0) =>
                                      case f of
                                        Fs (f,_) => f [s1,s2] >>>= (fn s => k(s,G2++G1++G0))
                                      | _ => raise Fail "comp.AppOpr2E: expecting function")))
            | IdE(Symb L.Slash) => 
              k(Fs (fn [Fs (f,ii)] =>
                       rett(Fs (fn [Ais x] => M(reduce Int (fn (x,y) =>
                                                        subM(f[Is x,Is y] >>>= (fn Is z => rett z
                                                                                 | _ => raise Fail "comp.Slash: expecting integer as result")))
                                                    (I(id_item_int ii)) x Is Ais)
                                 | [Ads x] => M(reduce Double (fn (x,y) =>
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
            | IdE(Symb L.Dot) =>
              k(Fs (fn [Fs(f1,ii),Fs(f2,_)] =>
                       rett(Fs (fn [Ais a1, Ais a2] => 
                                   M(prod Int (fn (x,y) =>  
                                                  subM(f1[Is x,Is y] >>>= (fn Is z => rett z
                                                                          | _ => raise Fail "comp.Dot: expecting int as result")))
                                          (fn (x,y) =>  
                                              subM(f2[Is x,Is y] >>>= (fn Is z => rett z
                                                                      | _ => raise Fail "comp.Dot: expecting int as result")))
                                          (I(id_item_int noii)) a1 a2 Is Ais)
                               | _ => raise Fail "comp.Dot: expecting two arrays",
                                noii))
                     | _ => raise Fail "comp.Dot: expecting two functions",
                    noii),
                emp)
            | IdE(Symb L.Each) => 
              k(Fs (fn [Fs (f,_)] =>
                       let exception No
                           fun tryInt t g x =
                               each t Int (fn x => case f[g x] of S(Is v) => ret v
                                                           | _ => raise No) x
                           fun tryDouble t g x =
                               each t Double (fn x => case f[g x] of S(Ds v) => ret v
                                                          | _ => raise Fail "Not Ds") x
                       in rett(Fs (fn [Ais x] => (S(Ais(tryInt Int Is x)) handle No => S(Ads(tryDouble Int Is x)))
                                    | [Ads x] => (S(Ais(tryInt Double Ds x)) handle No => S(Ads(tryDouble Double Ds x)))
                                    | _ => raise Fail "comp.Each: expecting array",
                                   noii))
                       end
                     | _ => raise Fail "comp.Each: expecting function as operator argument",
                    noii), 
                emp)
            | IdE(Symb L.Iota) => compPrimFunM k (fn Is i => S(Ais(iota i))
                                                   | Ais a => S(Ais(iota' a))
                                                   | _ => raise Fail "comp.Iota: expecting integer argument")
            | IdE(Symb L.Trans) => compPrimFunMD k (fn Ais a => S(Ais(transpose a))
                                                     | Ads a => S(Ads(transpose a))
                                                     | Abs a => S(Abs(transpose a))
                                                     | _ => raise Fail "comp.Trans: expecting array",
                                                    fn (Ais a1, Ais a2) => S(Ais(transpose2 (rav0 a1) a2))
                                                     | (Ais a1, Ads a2) => S(Ads(transpose2 (rav0 a1) a2))
                                                     | (Ais a1, Abs a2) => S(Abs(transpose2 (rav0 a1) a2))
                                                     | _ => raise Fail "comp.Dual transpose expects arrays") noii
            | IdE(Symb L.Rho) => compPrimFunMD k (fn Ais a => S(Ais(vec(shape a)))
                                                   | Ads a => S(Ais(vec(shape a)))
                                                   | Abs a => S(Ais(vec(shape a)))
                                                   | _ => raise Fail "comp.Rho.shape expects an array",
                                                  fn (Ais a1, Ais a2) => M(reshape (rav0 a1) a2) >>>= (fn a => rett(Ais a))
                                                   | (Ais a1, Ads a2) => M(reshape (rav0 a1) a2) >>>= (fn a => rett(Ads a))
                                                   | (Ais a1, Abs a2) => M(reshape (rav0 a1) a2) >>>= (fn a => rett(Abs a))
                                                   | _ => raise Fail "comp.Rho.reshape expects arrays") noii
            | IdE(Symb L.Cat) => compPrimFunMD k (fn Ais a => S(Ais(rav a))
                                                   | Ads a => S(Ads(rav a))
                                                   | Abs a => S(Abs(rav a))
                                                   | _ => raise Fail "comp.Cat.rav expects an array",
                                                  compOpr2_a8a2aM catenate catenate catenate) noii
            | IdE(Symb L.Disclose) => compPrimFunM k (fn Ais a => S(Is(first a))
                                                       | Ads a => S(Ds(first a))
                                                       | Abs a => S(Bs(first a))
                                                       | Is a => S(Is a)
                                                       | Ds a => S(Ds a)
                                                       | Bs a => S(Bs a)
                                                       | _ => raise Fail "comp.Disclose expects an array or a scalar")
            | IdE(Symb L.Take) => compPrimFunD k (compOpr2_i8a2a e take take take) noii
            | IdE(Symb L.Drop) => compPrimFunD k (compOpr2_i8a2a e drop drop drop) noii
            | IdE(Symb L.Rot) => compPrimFunMD k (fn Ais a => S(Ais(reverse a))
                                                   | Ads a => S(Ads(reverse a))
                                                   | Abs a => S(Abs(reverse a))
                                                   | _ => raise Fail "comp.Rot: expecting array",
                                                  compOpr2_i8a2a e rotate rotate rotate) noii
            | IdE(Symb L.Add) => compPrimFunMD k (S,
                                                  compOpr2 addi addd) noii
            | IdE(Symb L.Sub) => compPrimFunMD k (compOpr1 negi negd,
                                                  compOpr2 subi subd) noii
            | IdE(Symb L.Times) => compPrimFunMD k (compOpr1i signi signd,
                                                    compOpr2 muli muld) (LRii 1,LRii 1.0,NOii)
            | IdE(Symb L.Div) => compPrimFunMD k (compOpr1d (fn x => divd(D 1.0,x)),
                                                  compOpr2 divi divd) (LRii 1,LRii 1.0,NOii)
            | IdE(Symb L.Max) => compPrimFunD k (compOpr2 (uncurry maxi) (uncurry maxd)) (LRii(minInt()), LRii(Real.negInf),NOii)
            | IdE(Symb L.Min) => compPrimFunD k (compOpr2 (uncurry mini) (uncurry mind)) (LRii(maxInt()), LRii(Real.posInf),NOii)
            | IdE(Symb L.Lt) => compPrimFunD k (compCmp lti ltd) (NOii,NOii,NOii)
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
        and compLam22 G e (f,g) =
            rett(Fs(fn [x,y] =>
                       let val G' = [(Symb L.Alphaalpha, f),(Symb L.Omegaomega, g),(Symb L.Omega, y),(Symb L.Alpha, x)]
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
                                  Ais im => red Int Int (ret o addi) (I 0) im >>= (fn x => ret (i2d x))
                                | Ads dm => red Double Double (ret o addd) (D 0.0) dm
                                | Is i => ret (i2d i)
                                | Ds d => ret d
                                | _ => raise Fail "expecting array")
    in runM Double c'
    end
end

fun flag_p flags s =
    List.exists (fn p => p = (s,NONE)) flags

fun flag flags s =
    case List.find (fn (s',_) => s' = s) flags of
        SOME (_,SOME v) => SOME v
      | _ => NONE

fun compileAndRun flags s =
    let val compile_only_p = flag_p flags "-c"
        val verbose_p = flag_p flags "-v"
        val outfile = flag flags "-o"
        val ts = AplLex.lex s
        fun pr f = if verbose_p then prln(f()) else ()
        val () = pr (fn () => "Program lexed:")
        val () = pr (fn () => " " ^ AplLex.pr_tokens (map #1 ts))
        val () = pr (fn () => "Parsing tokens...")
    in case AplParse.parse AplParse.env0 ts of
         SOME (e,_) => 
         (pr(fn () => "Parse success:\n " ^ AplAst.pr_exp e);
          let val p = compileAst e
              val () =
                  case outfile of
                    SOME ofile => X.outprog ofile p
                  | NONE => ()
          in if compile_only_p then ()
             else let val () = prln("Evaluating")
                      val v = X.eval p X.Uv
                  in prln("Result is " ^ X.ppV v)
                  end
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

fun compileAndRunFile flags f =
    let val () = prln ("Reading file: " ^ f)
        val c = readFile f
    in compileAndRun flags c
    end

end
