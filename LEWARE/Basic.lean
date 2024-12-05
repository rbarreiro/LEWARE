
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

inductive Dependency where
  | import_ (s: String)
  | script (s: String)
deriving Repr

inductive HasVar : Env → String -> Ltype → Type where
  | here : HasVar (⟨name, t⟩ :: r) name t
  | there : HasVar s name t → HasVar (h :: s) name t
deriving Repr

mutual
  inductive Lexp : Target -> Env → Ltype → Type where
    | lit : Lit α → Lexp t e α
    | llet : (n : String) → (v : Lexp t e α) → (body : Lexp t ((n, α) :: e) β) -> Lexp t e β
    | var : (n : String) → (p : HasVar e n α) → Lexp t e α
    | listnil : Lexp t e (Ltype.list α)
    | listcons : Lexp t e α → Lexp t e (Ltype.list α) → Lexp t e (Ltype.list α)
    | recordnil : Lexp t e (Ltype.record [])
    | recordcons : (n : String) → Lexp t e α → Lexp t e (Ltype.record ts) → Lexp t e (Ltype.record ((n, α) :: ts))
    | mk : (n : String) → Lexp t e α → (p : HasVar ts n α) → Lexp t e (Ltype.sum ts)
    | lambda : (n : String) → Lexp t ((n, α) :: e) β → Lexp t e (α ⟶ β)
    | lmatch : Lexp t e (.sum ts) → LMatch t e ts β → Lexp t e β
    | relax : Lexp t e α → Lexp t (x::e) α
    | prim0 : List Dependency → String → Lexp t e α
    | prim1 : List Dependency → String -> Lexp t e β → Lexp t e α
    | prim2 : List Dependency → String -> Lexp t e β → Lexp t e γ → Lexp t e α
    | prim3 : List Dependency → String -> Lexp t e a → Lexp t e b → Lexp t e c → Lexp t e α
    | prim4 : List Dependency → String -> Lexp t e a → Lexp t e b → Lexp t e c → Lexp t e d → Lexp t e α
  deriving Repr

  inductive LMatch : Target → Env → List (String × Ltype) → Ltype → Type where
    | matchnil : LMatch t e [] β
    | matchcons : LMatch t e ts β → (n : String) → (v : String) → Lexp t ((v, α) :: e) β → LMatch t e ((n, α) :: ts) β
end

macro "cons(" n:term "," v:term ")" : term => `(Lexp.mk $n $v (by repeat constructor))
macro "var(" n:term ")" : term => `(Lexp.var $n (by repeat constructor))
macro "llet" n:term ":=" v:term ";" b:term : term => `(Lexp.llet ($n) ($v) ($b))

abbrev the (α : Ltype) (v: Lexp t e α ) : Lexp t e α :=
  v

macro "llet" n:term ":::" t:term ":=" v:term ";" b:term : term => `(Lexp.llet ($n) (the $t ($v)) ($b))
macro "var(" n:term ":::" t:term ")" : term => `(the $t (Lexp.var $n (by repeat constructor)))


syntax (priority := high) "lwith" "{" term,* "}" : term
macro_rules
  | `(lwith{}) => `(LMatch.matchnil)
  | `(lwith{($x > $y) = $z}) => `(LMatch.matchcons LMatch.matchnil $x $y $z)
  | `(lwith{($x > $y) = $z, $xs:term,*}) => `(LMatch.matchcons lwith{$xs,*} $x $y $z)


instance : Coe String (Lexp t e Ltype.string) where
  coe x := .lit (.str x)

def branch (cond : Lexp t e (.boolean)) (x : Lexp t e α) (y : Lexp t e α) : Lexp t e α :=
  match t with
    | .js _ => .prim3 [] "({arg0} ? {arg1} : {arg2})" cond x y
    | .rethinkdb => .prim3 [] "r.branch({arg0}, {arg1}, {arg2})" cond x y

macro c:term "??" t:term ":" e:term : term => `(branch ($c) ($t) ($e))

def unit : Lexp t e .unit :=
  match t with
    | .js _ => .prim0 [] "null"
    | .rethinkdb => .prim0 [] "r.expr(null)"

def none : Lexp t e (option α)  :=
  cons("none", unit)

def t2 (x0 : Lexp t e α) (x1 : Lexp t e β) : Lexp t e (.tuple [α, β]) :=
  match t with
    | .js _ => .prim2 [] "[{arg0}, {arg1}]" x0 x1
    | .rethinkdb => .prim2 [] "r.expr([{arg0}, {arg1}])" x0 x1

def getTag : (n : String) → Lexp t e (Ltype.sum ts) → (p : HasVar ts n α) → Lexp t e (option α) :=
  match t with
    | .js _ => sorry
    | .rethinkdb => sorry

def findTag : (n : String) → Lexp t e (.list (.sum ts)) → (p : HasVar ts n α) → Lexp t e (option α) :=
  sorry

macro "findTag!" n:term "in" x:term : term => `(findTag ($n) ($x) (by repeat constructor))
macro "getTag!" n:term "in" x:term : term => `(getTag ($n) ($x) (by repeat constructor))

def fromOption (de : Lexp t e α) (o : Lexp t e (option α)) : Lexp t e α :=
  .lmatch o lwith {
    ("some" > "x") = var("x"),
    ("none" > "_") = .relax de
  }

class LEq (t : Target) (α : Ltype) where
  leq : Lexp t e α → Lexp t e α → Lexp t e .boolean

instance : LEq (.rethinkdb) .string where
  leq x y := .prim2 [] "{arg0}.eq({arg1})" x y

def elem [LEq .rethinkdb α]
  (x : Lexp .rethinkdb e α)
    (lst : Lexp .rethinkdb e (.list α))
      : (Lexp .rethinkdb e .boolean) :=
  Lexp.prim2 [] "{args1}.contains({arg0})" x lst

syntax (priority := high) "l[" term,* "]" : term
macro_rules
  | `(l[]) => `(Lexp.listnil)
  | `(l[$x]) => `(Lexp.listcons $x Lexp.listnil)
  | `(l[$x, $xs:term,*]) => `(Lexp.listcons $x l[$xs,*])


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



structure ToJsState where
  imports : List String
  scripts : List String
deriving Repr

def initS : ToJsState :=
  { imports := []
  , scripts := []
  }

def addIfNotPresent (s : String) (lst : List String) : List String :=
  if lst.contains s then
    lst
  else
    s :: lst

def useDep (d : Dependency) (s : ToJsState) : ToJsState :=
  match d with
    | .import_ x => {s with imports := addIfNotPresent x s.imports}
    | .script x => {s with scripts := addIfNotPresent x s.scripts}

def useDeps : List Dependency → ToJsState → ToJsState
  | (x::xs), s => useDeps xs (useDep x s)
  | [], s => s

def escape_string (s : String) : String :=
  let f := λ s c => match c with
                      | '\\' => s ++ "\\\\"
                      | '\n' => s ++ "\\n"
                      | '"' => s ++ "\\\""
                      | o => s ++ o.toString;
   "\"" ++ String.foldl f "" s ++ "\""

mutual
  def toJSRecordLit (e : Lexp (.js v) e α) : StateM ToJsState (Option (List String)) :=
    match e with
    | .recordnil =>
      return some []
    | .recordcons n x xs =>
      do
        let x_ <- toJS x
        let xs_ <- toJSRecordLit xs
        match xs_ with
          | .none => return none
          | .some xs__ => return some (s!"{n}: {x_}" :: xs__)
    | _ =>
      return none

  def matchToJS : LMatch (.js v) e ts β → StateM ToJsState String
    | .matchnil =>
      return ""
    | .matchcons rs n v x =>
      do
        let x_ <- toJS x
        sorry

  def toJS : (e : Lexp (.js v) e α) → StateM ToJsState String
    | .lit l =>
      match l with
        | .str s => return (escape_string s)
    | .llet n v b =>
      do
        let v_ <- toJS v
        let b_ <- toJS b
        return s!"const {n} = {v_};\n {b_}"
    | .var n _ =>
      return n
    | .relax z =>
      toJS z
    | .listnil =>
      return "Immutable.List()"
    | .listcons x xs =>
      do
        let x_ <- toJS x
        let xs_ <- toJS xs
        return s!"{xs_}.unshift({x_})"
    | .recordnil =>
      return "Immutable.Map()"
    | .recordcons n x xs =>
      do
        let w <- toJSRecordLit (.recordcons n x xs)
        match w with
          | .none =>
            do
              let x_ <- toJS x
              let xs_ <- toJS xs
              return s!"{xs_}.set({n}, {x_})"
          | .some ls =>
            let args := String.intercalate "," ls
            let args := "{" ++ args ++ "}"
            return s!"Immutable.Map({args})"
    | .mk k v _ =>
      do
        let v_ <- toJS v
        return  "{" ++ s!"{k}: {v_}" ++ "}"
    | .lambda n b =>
      do
        let b_ <- toJS b
        return s!"function({n})" ++ "{" ++ s!"return {b_}" ++ "}"
    | .lmatch x m =>
      sorry
    | .prim0 deps template =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        return template
    | .prim1 deps template arg0 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toJS arg0
        return template.replace "{arg0}" arg0_
    | .prim2 deps template arg0 arg1 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toJS arg0
        let arg1_ <- toJS arg1
        return (template.replace "{arg0}" arg0_).replace "{arg1}" arg1_
    | .prim3 deps template arg0 arg1 arg2 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toJS arg0
        let arg1_ <- toJS arg1
        let arg2_ <- toJS arg2
        return ((template.replace "{arg0}" arg0_).replace "{arg1}" arg1_).replace "{arg2}" arg2_
    | .prim4 deps template arg0 arg1 arg2 arg3 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toJS arg0
        let arg1_ <- toJS arg1
        let arg2_ <- toJS arg2
        let arg3_ <- toJS arg3
        return (((template.replace "{arg0}" arg0_).replace "{arg1}" arg1_).replace "{arg2}" arg2_).replace "{arg3}" arg3_
end

mutual
  def toRethinkRecordLit (e : Lexp .rethinkdb e α) : StateM ToJsState (Option (List String)) :=
    match e with
    | .recordnil =>
      return some []
    | .recordcons n x xs =>
      do
        let x_ <- toRethink x
        let xs_ <- toRethinkRecordLit xs
        match xs_ with
          | .none => return none
          | .some xs__ => return some (n :: (x_ :: xs__))
    | _ =>
      return none

  def matchToRethink : LMatch (.js v) e ts β → StateM ToJsState String
    | .matchnil =>
      return ""
    | .matchcons rs n v x =>
      do
        let x_ <- toJS x
        sorry

  def toRethink : (e : Lexp .rethinkdb e α) → StateM ToJsState String
    | .lit l =>
      match l with
        | .str s => return s!"r.expr({escape_string s})"
    | .llet n v b =>
      do
        let v_ <- toRethink v
        let b_ <- toRethink b
        return s!"{v_}.do(({n}=> ({b_})))"
    | .var n _ =>
      return n
    | .relax x =>
      toRethink x
    | .listnil =>
      return "r.expr([])"
    | .listcons x xs =>
      do
        let x_ <- toRethink x
        let xs_ <- toRethink xs
        return s!"{xs_}.insertAt({x_})"
    | .recordnil =>
      return "r.expr({})"
    | .recordcons n x xs =>
      do
        let w <- toRethinkRecordLit (.recordcons n x xs)
        match w with
          | .none =>
            do
              let x_ <- toRethink x
              let xs_ <- toRethink xs
              return s!"{xs_}.coerceTo('array').append([{n}, {x_}]).coerceTo('object')"
          | .some ls =>
            let args := String.intercalate "," ls
            return s!"r.object({args})"
    | .mk k v _ =>
      do
        let v_ <- toRethink v
        return  s!"r.object({k}, {v_})"
    | .lambda n b =>
      do
        let b_ <- toRethink b
        return s!"function({n})" ++ "{" ++ s!"return {b_}" ++ "}"
    | .lmatch x m =>
      sorry
    | .prim0 deps template =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        return template
    | .prim1 deps template arg0 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toRethink arg0
        return template.replace "{arg0}" arg0_
    | .prim2 deps template arg0 arg1 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toRethink arg0
        let arg1_ <- toRethink arg1
        return (template.replace "{arg0}" arg0_).replace "{arg1}" arg1_
    | .prim3 deps template arg0 arg1 arg2 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toRethink arg0
        let arg1_ <- toRethink arg1
        let arg2_ <- toRethink arg2
        return ((template.replace "{arg0}" arg0_).replace "{arg1}" arg1_).replace "{arg2}" arg2_
    | .prim4 deps template arg0 arg1 arg2 arg3 =>
      do
        modifyGet (λ s => ((), useDeps deps s))
        let arg0_ <- toRethink arg0
        let arg1_ <- toRethink arg1
        let arg2_ <- toRethink arg2
        let arg3_ <- toRethink arg3
        return (((template.replace "{arg0}" arg0_).replace "{arg1}" arg1_).replace "{arg2}" arg2_).replace "{arg3}" arg3_
end

def dbList : Lexp .rethinkdb e (.list .string) :=
  .prim0 [] "r.dbList()"

def dbCreate (name : Lexp .rethinkdb e .string) : Lexp .rethinkdb e (.record [("dbs_created", .nat)]) :=
  .prim1 [] "r.dbCreate({arg0})" name

def tableList (db : Lexp .rethinkdb e .string) : Lexp .rethinkdb e (.list .string) :=
  .prim1 [] "r.db({arg0}).tableList()" db

def tableCreate (db : Lexp .rethinkdb e .string)
                  (name : Lexp .rethinkdb e .string)
                      : Lexp .rethinkdb e (.record [("tables_created", .nat)]) :=
  .prim2 [] "r.db({arg0}).tableCreate({arg1})" db name

def genInitDB (schemaName : String) (sch : Schema) : Lexp .rethinkdb [] .unit :=
  llet "_" := dbCreate "leware";
  llet "_" := dbCreate (.lit (.str schemaName));
  llet "_" := sch.foldl (λ e (n, _, _) => llet "_" := tableCreate (.lit (.str schemaName)) (.lit (.str n)) ; .relax e) unit;
  unit

def genSchemaMigrationQuery (schemaDef : SchemaDef σ) : Lexp .rethinkdb [] .unit :=
  match schemaDef with
    | .new name sch =>
      elem "leware" dbList ?? unit :
        genInitDB name sch

def genSchemaMigration (schemaDef : SchemaDef σ) : StateM ToJsState String :=
  do
    let q : Lexp .rethinkdb [] .unit := genSchemaMigrationQuery schemaDef
    let qs <- toRethink q
    return s!"{qs}.run(connection, function(err, result)\{})"

def genReactDef : ReactDef servs e name fs β → StateM ToJsState String
  | .widget name args body =>
    do
      let b <- toJS body
      let b_ := "{\n return " ++ b ++ "\n}"
      return s!"function {name}(){b_}"
  | .function name args body =>
    do
      let b <- toJS body
      let b_ := "{\n return " ++ b ++ "\n}"
      return s!"function {name}(){b_}"

def genReactApp : ReactApp servs e → StateM ToJsState String
  | .appnil _ =>
    return ""
  | .appcons x y =>
    do
      let x_ <- genReactApp x
      let y_ <- genReactDef y
      return x_ ++ "\n\n" ++ y_
