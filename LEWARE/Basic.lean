
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
  | record (fs : List (String × Ltype))
  | sum (fs : List (String × Ltype))
  | func (a : Ltype) (b : Ltype)
  | event
deriving Repr

infixr:10   " ⟶ " => Ltype.func

def option (α : Ltype) : Ltype := .sum [("some", α), ("none", .unit)]

abbrev Env := List (String × Ltype)

inductive Lit : LType → Type where
  | str : String → Lit (Ltype.string)
deriving Repr

inductive JSTarget where
  | node
  | react
deriving Repr

inductive Target where
  | js (v : JSTarget)
  | rethinkdb
deriving Repr

abbrev react := Target.js .react


inductive HasVar : Env → String -> Ltype → Type where
  | here : HasVar (⟨name, t⟩ :: r) name t
  | there : HasVar s name t → HasVar (h :: s) name t
deriving Repr

inductive Dependency where
  | declaration : String → String → Dependency
deriving Repr

mutual

  inductive Lexp : Target -> Env → Ltype → Type where
    | lit : Lit α → Lexp t e α
    | llet : (n : String) → (v : Lexp t e α) → (body : Lexp t ((n, α) :: e) β) -> Lexp t e β
    | var : (n : String) → (p : HasVar e n α) → Lexp t e α
    | listnil : Lexp t e (.list α)
    | listcons : Lexp t e (α ⟶ .list α ⟶ .list α)
    | recordnil : Lexp t e (Ltype.record [])
    | recordcons : (n : String) → Lexp t e α → Lexp t e (Ltype.record ts) → Lexp t e (Ltype.record ((n, α) :: ts))
    | mk : (n : String) → Lexp t e α → (p : HasVar ts n α) → Lexp t e (Ltype.sum ts)
    | lambda : (n : String) → Lexp t ((n, α) :: e) β → Lexp t e (α ⟶ β)
    | lmatch : Lexp t e (.sum ts) → LMatch t e ts β → Lexp t e β
    | relax : Lexp t e α → Lexp t (x::e) α
    | app : Lexp t e (α ⟶ β) → Lexp t e α → Lexp t e β
    | prim : List Dependency → String → Lexp t e α
    | primWithExp2Decl : List Dependency → (name : String) → (template : String) → Lexp t e1 γ → Lexp t e2 μ → String → Lexp t e α
  deriving Repr

  inductive LMatch : Target → Env → List (String × Ltype) → Ltype → Type where
    | matchnil : LMatch t e [] β
    | matchcons : LMatch t e ts β → (n : String) → (v : String) → Lexp t ((v, α) :: e) β → LMatch t e ((n, α) :: ts) β
end

syntax (priority := high) "func" ident,+ "=>" term : term
macro_rules
  | `(func $n => $b) => `(Lexp.lambda $(Lean.quote (toString n.getId)) ($b))
  | `(func $n, $ns:ident,* => $b) => `(Lexp.lambda $(Lean.quote (toString n.getId)) (func $ns,* => $b))

infixl:100 " @@ " => Lexp.app

macro "cons(" n:ident "," v:term ")" : term => `(Lexp.mk $(Lean.quote (toString n.getId)) $v (by repeat constructor))
macro "&" n:ident : term => `(Lexp.var $(Lean.quote (toString n.getId)) (by repeat constructor))
macro "llet" n:ident ":=" v:term ";" b:term : term => `(Lexp.llet $(Lean.quote (toString n.getId)) ($v) ($b))

abbrev the (α : Ltype) (v: Lexp t e α ) : Lexp t e α :=
  v

macro "llet" n:ident ":::" t:term ":=" v:term ";" b:term : term => `(Lexp.llet $(Lean.quote (toString n.getId)) (the $t ($v)) ($b))
macro "&(" n:ident ":::" t:term ")" : term => `(the $t (Lexp.var $(Lean.quote (toString n.getId)) (by repeat constructor)))


syntax (priority := high) "||" ident ident "=>" term : term
syntax (priority := high) "lwith" "{" term,* "}" : term
macro_rules
  | `(lwith{}) => `(LMatch.matchnil)
  | `(lwith{|| $x $y => $z}) => `(LMatch.matchcons LMatch.matchnil $(Lean.quote (toString x.getId)) $(Lean.quote (toString y.getId)) $z)
  | `(lwith{|| $x $y => $z, $xs:term,*}) => `(LMatch.matchcons (lwith {$xs,*}) $(Lean.quote (toString x.getId)) $(Lean.quote (toString y.getId)) $z)

macro "lmatch" "(" x:term ")" y:term : term => `(Lexp.lmatch ($x) ($y))

instance : Coe String (Lexp t e Ltype.string) where
  coe x := .lit (.str x)

def branch : Lexp t e (.boolean ⟶ α ⟶ α ⟶ α) :=
  match t with
    | .js _ => .prim [.declaration "branch" "const branch = (cond => (x => (y => cond ? x : y))) ;"] "branch"
    | .rethinkdb => .prim [.declaration "r_branch" "const r_branch = (cond => (x => (y => r.branch(cond, x, y))));"] "r_branch"

macro c:term "??" t:term ":" e:term : term => `(branch @@ $c @@ $t @@ $e)

def unit : Lexp t e .unit :=
  match t with
    | .js _ => .prim [] "null"
    | .rethinkdb => .prim [] "r.expr(null)"

def none : Lexp t e (option α)  :=
  cons(none, unit)

def some : Lexp t e (α ⟶ option α)  :=
  func x =>
    cons(some, &x)

def t2 : Lexp t e (α ⟶ β ⟶ .tuple [α, β]) :=
  match t with
    | .js _ => .prim [.declaration "t2" "const t2 = (x => (y=>[x,y]));"] "t2"
    | .rethinkdb => .prim [.declaration "r_t2" "const r_t2 = (x => (y=>r.expr([x,y])));"] "r_t2"

def fromOption : Lexp t e (α ⟶ option α ⟶ α) :=
  func d, z =>
    lmatch (&z) lwith {
      || some x => &x,
      || none x => &d
    }

class LFunctor (t : Target) (f : Ltype → Ltype) where
  map : Lexp t e ((α ⟶ β) ⟶ f α ⟶ f β)

class LEq (t : Target) (α : Ltype) where
  leq : Lexp t e (α ⟶ α ⟶ .boolean)

class LAppend (t : Target) (α : Ltype) where
  lappend : Lexp t e (α ⟶ α ⟶ α)

macro x:term "+++" y:term : term => `(LAppend.lappend @@ $x @@ $y)

instance : LEq (.rethinkdb) .string where
  leq :=
    .prim [.declaration "r_string_leq" "const r_string_leq = x =>(y=> x.eq(y)));"] "r_string_leq"

instance : LFunctor (Target.js v) option where
  map := func f, x =>
    lmatch (&x) lwith{
      || some y => some @@ (&f @@ &y),
      || none y => none
    }

instance : LAppend (Target.js v) (.list α) where
  lappend :=
    .prim [.declaration "lappend" "const lappend = x=>(y=>x.concat(y));"] "lappend"

instance : LFunctor (Target.js v) .list where
  map :=
    .prim [.declaration "list_map" "const list_map = f => (x => x.map(f));" ] "list_map"

def elem [LEq .rethinkdb α] : Lexp .rethinkdb e (α ⟶ .list α ⟶ .boolean) :=
  Lexp.prim [.declaration "r_elem" "const r_elem = x => (y => x.contains(y));"] "r_elem"

def flatMap : Lexp t e ((α ⟶ .list β) ⟶ .list α ⟶ .list β) :=
  match t with
    | .js _ => .prim [.declaration "flatMap" "const flatMap = f => (l => l.flatMap(f));"] "flatMap"
    | .rethinkdb => .prim [.declaration "r_flatMap" "const r_flatMap = f => (l => l.flatMap(f));"] "r_flatMap"


syntax (priority := high) "l[" term,* "]" : term
macro_rules
  | `(l[]) => `(Lexp.listnil)
  | `(l[$x]) => `(Lexp.listcons @@ $x @@ Lexp.listnil)
  | `(l[$x, $xs:term,*]) => `(Lexp.listcons @@ $x @@ l[$xs,*])


syntax (priority := high) "r{" term,* "}" : term
macro_rules
  | `(r{}) => `(Lexp.recordnil)
  | `(r{$x = $y}) => `(Lexp.recordcons $x $y Lexp.recordnil)
  | `(r{$x = $y, $xs:term,*}) => `(Lexp.recordcons $x $y r{$xs,*})

abbrev Schema := List (String × Ltype × Ltype)

abbrev schemaEnv (x : Schema) : Env :=
  x.map (λ (n, k, v) => (n, Ltype.table k v))

inductive SchemaDef : Schema → Type where
  | new : String → (l : Schema) → SchemaDef l
deriving Repr

inductive AccessPolicy where
  | all
  | roles (list : List String)
deriving Repr

structure ServiceTy where
  name : String
  args : Env
  res : Ltype
  roles : AccessPolicy
deriving Repr

inductive ServiceDef : Schema → Env → ServiceTy → Type where
  | service : (α : ServiceTy) →
                Lexp (.js .node) (α.args ++ schemaEnv σ ++ e) α.res →
                  ServiceDef σ e α
  | dbService : (α : ServiceTy) →
                Lexp .rethinkdb (α.args ++ schemaEnv σ ++ e) α.res →
                  ServiceDef σ e α
deriving Repr

abbrev servicesEnv (x : List ServiceTy) : Env :=
  List.map (λ y => (y.name , Ltype.record y.args ⟶ y.res)) x

inductive Server : Schema → List ServiceTy → Type where
  | base : SchemaDef σ → Server σ []
  | addService : Server σ l → ServiceDef σ (servicesEnv l) t → Server σ (t :: l)
deriving Repr

syntax (priority := high) "#server" "[" term "]" "{" term,* "}" : term
macro_rules
  | `(#server[$z]{}) => `(Server.base $z)
  | `(#server[$z]{$x}) => `(Server.addService (Server.base $z) $x)
  | `(#server[$z]{$xs:term,*, $x}) => `(Server.addService #server[$z]{$xs,*} $x)

/-
inductive ReactDef : List ServiceTy → Env → String → List (String × Ltype) → Ltype → Type where
  | widget : (name : String) →
                (fs : List (String × Ltype)) →
                  Lexp react (fs ++ e) .node →
                    ReactDef servs e name fs .node
  | function : (name : String) →
                (fs : List (String × Ltype)) →
                  Lexp react (fs ++ e) β →
                    ReactDef servs e name fs β
deriving Repr

inductive ReactApp : List ServiceTy → Env → Type where
  | appnil : Server σ servs → ReactApp servs []
  | appcons : ReactApp servs d → ReactDef servs d name fs β →
                ReactApp servs ((name, Ltype.record fs ⟶ β) :: d)
deriving Repr

syntax (priority := high) "#app" "[" term "]" "{" term,* "}" : term
macro_rules
  | `(#app[$z]{}) => `(ReactApp.appnil $z)
  | `(#app[$z]{$x}) => `(ReactApp.appcons (ReactApp.appnil $z) $x)
  | `(#app[$z]{$xs:term,*, $x}) => `(ReactApp.appcons #app[$z]{$xs,*} $x)

-/

inductive AppPath where
  | root : AppPath

inductive Router : Env → List AppPath → Type where
  | nil : Router e []
  | cons : (p : AppPath) → Lexp react e .node → Router e l → Router e (p :: l)

syntax (priority := high) "r[" term,* "]" : term
macro_rules
  | `(r[]) => `(Router.nil)
  | `(r[$x]) => `(let w := $x; Router.cons (w.fst) (w.snd) Router.nil)
  | `(l[$x, $xs:term,*]) => `(let w := $x; Router.cons (Prod.fst w) (Prod.snd w) r[$xs,*])


inductive ReactApp where
  | mk : Server σ γ → (paths : List AppPath) → Router [] paths → ReactApp

syntax "#app" "[" term "]" "{" term,* "}" : term

macro_rules
  | `(#app [$z] { $[$x:term],* }) => `( ReactApp.mk $z [ $[Prod.fst $x],* ]  r[ $[$x],* ])

def dbList : Lexp .rethinkdb e (.list .string) :=
  .prim [] "r.dbList()"

def dbCreate : Lexp .rethinkdb e (.string ⟶ .record [("dbs_created", .nat)]) :=
  .prim [] "r.dbCreate"

def tableList : Lexp .rethinkdb e (.string ⟶ .list .string) :=
  .prim [.declaration "r_tableList" "const r_tableList = x => r.db(x).tableList();"] "r_tableList"

def tableCreate : Lexp .rethinkdb e (.string ⟶ .string ⟶ .record [("tables_created", .nat)]) :=
  .prim [.declaration "r_tableCreate" "const r_tableCreate = x => (y => r.db(x).tableCreate(y));"] "r_tableCreate"
