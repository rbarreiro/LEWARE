import Lean.Data.Json

open Lean
open Json

inductive Ltype where
  | unit
  | string
  | nat
  | node
  | boolean
  | datetime
  | table (k : Ltype) (v : Ltype)
  | tuple (xs : List Ltype)
  | list (α : Ltype)
  | io (α : Ltype)
  | signal (α : Ltype)
  | record (fs : List (String × Ltype))
  | sum (fs : List (String × Ltype))
  | func (a : Ltype) (b : Ltype)
  | event
deriving Repr, ToJson

infixr:10   " ⟶ " => Ltype.func

def option (α : Ltype) : Ltype := .sum [("some", α), ("none", .unit)]

inductive GenType where
  | base : Ltype → GenType
  | parametric : (g: Ltype → Ltype) → GenType
  | parametric2 : (g: Ltype → Ltype → Ltype) → GenType

abbrev Env := List (String × GenType)

abbrev Fields := List (String × Ltype)

abbrev toEnv (fs : Fields) : Env :=
  fs.map (λ (n, t) => (n, GenType.base t))

inductive Lit : LType → Type where
  | str : String → Lit (Ltype.string)
  | unit : Lit Ltype.unit
deriving Repr

inductive HasGenVar : Env → String -> GenType → Type where
  | here : HasGenVar (⟨name, t⟩ :: r) name t
  | there : HasGenVar s name t → HasGenVar (h :: s) name t
deriving Repr

inductive HasField : List (String × Ltype) → String -> Ltype → Type where
  | here : HasField (⟨name, t⟩ :: r) name t
  | there : HasField s name t → HasField (h :: s) name t
deriving Repr

abbrev HasVar e n α := HasGenVar e n (GenType.base α)

mutual
  inductive LMatch : Env → List (String × Ltype) → Ltype → Type where
    | matchnil : LMatch e [] β
    | matchcons : LMatch e ts β → (n : String) → (v : String) → Lexp ((v, .base α) :: e) β → LMatch e ((n, α) :: ts) β
  deriving Repr

  inductive Ldo : Env → Ltype → Type where
    | base : Lexp e (.io α) → Ldo e α
    | bind : (n : String) → (v : Lexp e (.io α)) → Ldo ((n, .base α) :: e) β → Ldo e β
    | seq : Lexp e (.io .unit) → Ldo e β → Ldo e β
  deriving Repr

  inductive Lexp : Env → Ltype → Type where
    | lit : Lit α → Lexp e α
    | llet : (n : String) → (v : Lexp e α) → (body : Lexp ((n, .base α) :: e) β) -> Lexp e β
    | var : (n : String) → (p : HasVar e n α) → Lexp e α
    | parametricVar : (n : String) → (α : Ltype) → (p : HasGenVar e n (GenType.parametric g)) → Lexp e (g α)
    | parametric2Var : (n : String) → (α : Ltype) → (β : Ltype) → (p : HasGenVar e n (GenType.parametric2 g)) → Lexp e (g α β)
    | listnil : Lexp e (.list α)
    | listcons : Lexp e (α ⟶ .list α ⟶ .list α)
    | recordnil : Lexp e (Ltype.record [])
    | recordcons : (n : String) → Lexp e α → Lexp e (Ltype.record ts) → Lexp e (Ltype.record ((n, α) :: ts))
    | recordGet : (n : String) → Lexp e (Ltype.record ts) → HasField ts n α → Lexp e α
    | mk : (n : String) → Lexp e α → (p : HasField ts n α) → Lexp e (Ltype.sum ts)
    | lambda : (n : String) → Lexp ((n, .base α) :: e) β → Lexp e (α ⟶ β)
    | lmatch : Lexp e (.sum ts) → LMatch e ts β → Lexp e β
    | ldo : Ldo e α → Lexp e (.io α)
    | relax : Lexp e α → Lexp (x::e) α
    | app : Lexp e (α ⟶ β) → Lexp e α → Lexp e β
    | branch : Lexp e (.boolean ⟶ α ⟶ α ⟶ α)
    | t2 : Lexp e (α ⟶ β ⟶ .tuple [α, β])
    | strEq : Lexp e (.string ⟶ .string ⟶ .boolean)
    | listAppend : Lexp e (.list α ⟶ .list α ⟶ .list α)
    | listMap : Lexp e ((α ⟶ β) ⟶ .list α ⟶ .list β)
    | elem : Lexp e (α ⟶ .list α ⟶ .boolean)
    | foldl : Lexp e ((α ⟶ β ⟶ β) ⟶ β ⟶ .list α ⟶ β)
    | iopure : Lexp e (α ⟶ .io α)
    | signalpure : Lexp e (α ⟶ .signal α)
    | lastValue : Lexp e (.signal α ⟶ .io α)
    | findTag : String → Lexp e (.list (.sum ts)) → HasField ts tag α → Lexp e (option α)
  deriving Repr
end

instance : ToJson (Lit α) where
  toJson
    | Lit.str s => toJson [Json.str "str", toJson s]
    | Lit.unit => toJson [Json.str "unit"]

mutual
  def lmatchToJson : LMatch e ts β → Json
    | .matchnil => toJson [Json.str "matchnil"]
    | .matchcons rs n v x => toJson [Json.str "matchcons", toJson n, toJson v, lexpToJson x, lmatchToJson rs]

  def ldoToJson : Ldo e α → Json
    | Ldo.base x => toJson [Json.str "dobase", lexpToJson x]
    | Ldo.bind n v x => toJson [Json.str "dobind", toJson n, lexpToJson v, ldoToJson x]
    | Ldo.seq x y => toJson [Json.str "doseq", lexpToJson x, ldoToJson y]

  def lexpToJson : Lexp e α → Json
    | Lexp.lit l => toJson [Json.str "lit", toJson l]
    | Lexp.llet n v b => toJson [Json.str "llet", toJson n, lexpToJson v, lexpToJson b]
    | Lexp.var n p => toJson [Json.str "var", toJson n]
    | Lexp.parametricVar n α p => toJson [Json.str "parametricVar", toJson n]
    | Lexp.parametric2Var n α β p => toJson [Json.str "parametric2Var", toJson n]
    | Lexp.listnil => toJson [Json.str "listnil"]
    | Lexp.listcons => toJson [Json.str "listcons"]
    | Lexp.recordnil => toJson [Json.str "recordnil"]
    | Lexp.recordcons n x xs => toJson [Json.str "recordcons", toJson n, lexpToJson x, lexpToJson xs]
    | Lexp.recordGet n x p => toJson [Json.str "recordGet", toJson n, lexpToJson x]
    | Lexp.mk n v p => toJson [Json.str "mk", toJson n, lexpToJson v]
    | Lexp.lambda n b => toJson [Json.str "lambda", toJson n, lexpToJson b]
    | Lexp.lmatch x m => toJson [Json.str "lmatch", lexpToJson x, lmatchToJson m]
    | Lexp.ldo x => toJson [Json.str "ldo", ldoToJson x]
    | Lexp.relax x => toJson [Json.str "relax", lexpToJson x]
    | Lexp.app f x => toJson [Json.str "app", lexpToJson f, lexpToJson x]
    | Lexp.branch => toJson [Json.str "branch"]
    | Lexp.t2 => toJson [Json.str "t2"]
    | Lexp.strEq => toJson [Json.str "strEq"]
    | Lexp.listAppend => toJson [Json.str "listAppend"]
    | Lexp.listMap => toJson [Json.str "listMap"]
    | Lexp.elem => toJson [Json.str "elem"]
    | Lexp.foldl => toJson [Json.str "foldl"]
    | Lexp.iopure => toJson [Json.str "iopure"]
    | Lexp.signalpure => toJson [Json.str "signalpure"]
    | Lexp.lastValue => toJson [Json.str "lastValue"]
    | Lexp.findTag t p v => toJson [Json.str "findTag", toJson t, lexpToJson p]
end

instance : ToJson (Lexp e α) where
  toJson := lexpToJson

syntax (priority := high) "{" term,* "}" : term
syntax (priority := high) "llet" ident "<-" term : term
macro_rules
  | `({$t}) => `(Ldo.base $t)
  | `({llet $x <- $y , $xs:term,*}) => `(Ldo.bind $(Lean.quote (toString x.getId)) $y ({$xs,*}))
  | `({$x , $xs:term,*}) => `(Ldo.seq $x ({$xs,*}))

syntax (priority := high) "func" ident,+ "=>" term : term
macro_rules
  | `(func $n => $b) => `(Lexp.lambda $(Lean.quote (toString n.getId)) ($b))
  | `(func $n, $ns:ident,* => $b) => `(Lexp.lambda $(Lean.quote (toString n.getId)) (func $ns,* => $b))

infixl:100 " @@ " => Lexp.app

macro "cons(" n:ident "," v:term ")" : term => `(Lexp.mk $(Lean.quote (toString n.getId)) $v (by repeat constructor))
macro "&" n:ident : term => `(Lexp.var $(Lean.quote (toString n.getId)) (by repeat constructor))
macro "llet" n:ident ":=" v:term ";" b:term : term => `(Lexp.llet $(Lean.quote (toString n.getId)) ($v) ($b))

abbrev the (α : Ltype) (v: Lexp e α ) : Lexp e α :=
  v

macro "llet" n:ident ":::" t:term ":=" v:term ";" b:term : term => `(Lexp.llet $(Lean.quote (toString n.getId)) (the $t ($v)) ($b))
macro "&(" n:ident ":::" t:term ")" : term => `(the $t (Lexp.var $(Lean.quote (toString n.getId)) (by repeat constructor)))
macro x:term ".." n:ident : term => `(Lexp.recordGet $(Lean.quote (toString n.getId)) $x (by repeat constructor))

syntax (priority := high) "||" ident ident "=>" term : term
syntax (priority := high) "lwith" "{" term,* "}" : term
macro_rules
  | `(lwith{}) => `(LMatch.matchnil)
  | `(lwith{|| $x $y => $z}) => `(LMatch.matchcons LMatch.matchnil $(Lean.quote (toString x.getId)) $(Lean.quote (toString y.getId)) $z)
  | `(lwith{|| $x $y => $z, $xs:term,*}) => `(LMatch.matchcons (lwith {$xs,*}) $(Lean.quote (toString x.getId)) $(Lean.quote (toString y.getId)) $z)

macro "lmatch" "(" x:term ")" y:term : term => `(Lexp.lmatch ($x) ($y))

instance : Coe String (Lexp e Ltype.string) where
  coe x := .lit (.str x)

instance : Coe String (Lexp e (.signal .string)) where
  coe x := .signalpure @@ x

macro c:term "??" t:term ":" e:term : term => `(Lexp.branch @@ $c @@ $t @@ $e)

def unit : Lexp e .unit :=
  .lit .unit

def none : Lexp e (option α)  :=
  cons(none, unit)

def some : Lexp e (α ⟶ option α)  :=
  func x =>
    cons(some, &x)

def fromOption : Lexp e (α ⟶ option α ⟶ α) :=
  func d, z =>
    lmatch (&z) lwith {
      || some x => &x,
      || none x => &d
    }

class LFunctor (f : Ltype → Ltype) where
  map : Lexp e ((α ⟶ β) ⟶ f α ⟶ f β)

class LEq (α : Ltype) where
  leq : Lexp e (α ⟶ α ⟶ .boolean)

class LAppend (α : Ltype) where
  lappend : Lexp e (α ⟶ α ⟶ α)

macro x:term "+++" y:term : term => `(LAppend.lappend @@ $x @@ $y)


instance : LEq .string where
  leq := .strEq

instance : LFunctor option where
  map := func f, x =>
    lmatch (&x) lwith{
      || some y => some @@ (&f @@ &y),
      || none y => none
    }

instance : LAppend (.list α) where
  lappend := .listAppend

instance : LFunctor .list where
  map := .listMap


syntax (priority := high) "l[" term,* "]" : term
macro_rules
  | `(l[]) => `(Lexp.listnil)
  | `(l[$x]) => `(Lexp.listcons @@ $x @@ Lexp.listnil)
  | `(l[$x, $xs:term,*]) => `(Lexp.listcons @@ $x @@ l[$xs,*])

def appendOption : Lexp e (.list α ⟶ option α ⟶ .list α) :=
  func l, y =>
    lmatch (&y) lwith {
      || some x => &l +++ l[&x],
      || none x => &l
    }

macro x:term "+++?" y:term : term => `(appendOption @@ $x @@ $y)

def flatMap : Lexp e ((α ⟶ .list β) ⟶ .list α ⟶ .list β) :=
  func f, x =>
    .foldl @@ (func accum, y => .listAppend @@ &accum @@ &y) @@ l[] @@ (.listMap @@ &f @@ &x)

syntax (priority := high) "r{" term,* "}" : term
macro_rules
  | `(r{}) => `(Lexp.recordnil)
  | `(r{$x = $y}) => `(Lexp.recordcons $x $y Lexp.recordnil)
  | `(r{$x = $y, $xs:term,*}) => `(Lexp.recordcons $x $y r{$xs,*})


class SubEnv (a : Env) (b : Env) where
  adaptVar : HasGenVar a n α → HasGenVar b n α

instance : SubEnv e e where
  adaptVar := id

instance [s : SubEnv a b] : SubEnv a (h :: b) where
  adaptVar x := HasGenVar.there (s.adaptVar x)

def adaptVarAppend (p : HasGenVar a n α) : HasGenVar (more ++ a) n α :=
  match more with
   | [] => p
   | _ :: rest => HasGenVar.there (@adaptVarAppend a n α rest p)

instance [s : SubEnv a b] : SubEnv a (more ++ b) where
  adaptVar x := adaptVarAppend (s.adaptVar x)

macro "findTag!" "(" t:ident "," x:term ")" : term =>
    `(Lexp.findTag $(Lean.quote (toString t.getId)) $x (by repeat constructor))
