import LEWARE.Basic


def attr : Ltype := .tuple [.string, .sum [("stringAttr", .string), ("eventHandler", .event ⟶ .io .unit)]]


abbrev insertResTy := Ltype.record [("inserted", .nat)]

abbrev react : Env :=
  [ ("node", .base (.string ⟶ .list attr ⟶ .list .node ⟶ .node))
  , ("text", .base (.string ⟶ .node))
  , ("targetValue", .base (.event ⟶ .io .string))
  , ("preventDefault", .base (.event ⟶ .io .unit))
  , ("widget", .parametric2 (λ s p => ((p ⟶ s ⟶ (s ⟶  .io .unit) ⟶ .node) ⟶ s ⟶ p ⟶ .node)))
  ]

def node [se : SubEnv react e] : Lexp e (.string ⟶ .list attr ⟶ .list .node ⟶ .node) :=
  let p : HasVar react "node" (.string ⟶ .list attr ⟶ .list .node ⟶ .node) := by repeat constructor
  Lexp.var "node" (se.adaptVar p)

def text [se : SubEnv react e] : Lexp e (.string ⟶ .node) :=
  let p : HasVar react "text" (.string ⟶ .node) := by repeat constructor
  Lexp.var "text" (se.adaptVar p)

def targetValue [se : SubEnv react e] : Lexp e (.event ⟶ .io .string) :=
  let p : HasVar react "targetValue" (.event ⟶ .io .string) := by repeat constructor
  Lexp.var "targetValue" (se.adaptVar p)

def preventDefault [se : SubEnv react e] : Lexp e (.event ⟶ .io .unit) :=
  let p : HasVar react "preventDefault" (.event ⟶ .io .unit) := by repeat constructor
  Lexp.var "preventDefault" (se.adaptVar p)

def widget [SubEnv react e]
            (init : Lexp e σ)
                (body : Lexp (("setState", .base (σ ⟶ .io .unit))
                               ::("state", .base σ)
                               :: ("props", .base (.list (.sum ts)))
                               :: e)
                              (.node))
                  : Lexp e (.list (.sum ts) ⟶ .node) :=
  let p : HasGenVar react "widget" (.parametric2 (λ s p => ((p ⟶ s ⟶ (s ⟶  .io .unit) ⟶ .node) ⟶ s ⟶ p ⟶ .node))) :=
          by repeat constructor
  let w : Lexp e ((.list (.sum ts) ⟶ σ ⟶ (σ ⟶  .io .unit) ⟶ .node) ⟶ σ ⟶ .list (.sum ts) ⟶ .node) :=
            Lexp.parametric2Var "widget" σ (.list (.sum ts)) (SubEnv.adaptVar p)
  w @@ (func props, state, setState => body) @@ init

abbrev serviceEnv : Env :=
  []

abbrev dbServiceEnv : Env :=
  [ ("insertIdValue", .parametric2 (λ i v => .table i v ⟶ i ⟶ v ⟶ .io insertResTy))
  , ("uuid", .base (.io .string))
  , ("now", .base (.io .datetime))
  ]

def insertIdValue [se : SubEnv dbServiceEnv e] : Lexp e (.table i v ⟶ i ⟶ v ⟶ .io insertResTy) :=
  let p : HasGenVar dbServiceEnv "insertIdValue" (.parametric2 (λ i v => .table i v ⟶ i ⟶ v ⟶ .io insertResTy)) :=
            by repeat constructor
  let w : Lexp e (.table i v ⟶ i ⟶ v ⟶ .io insertResTy) :=
            Lexp.parametric2Var "insertIdValue" i v (se.adaptVar p)
  w

def uuid [se : SubEnv dbServiceEnv e] : Lexp e (.io .string) :=
  let p : HasVar dbServiceEnv "uuid" (.io .string) := by repeat constructor
  Lexp.var "uuid" (se.adaptVar p)

def now [se : SubEnv dbServiceEnv e] : Lexp e (.io .datetime) :=
  let p : HasVar dbServiceEnv "now" (.io .datetime) := by repeat constructor
  Lexp.var "now" (se.adaptVar p)

abbrev Schema := List (String × Ltype × Ltype)

abbrev schemaEnv (x : Schema) : Fields :=
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
  args : Fields
  res : Ltype
  roles : AccessPolicy
deriving Repr


inductive ServiceDef : Schema → Env → ServiceTy → Type where
  | service : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ e ++ serviceEnv) (.io α.res) →
                  ServiceDef σ e α
  | dbService : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ e ++ dbServiceEnv) (.io α.res) →
                  ServiceDef σ e α
deriving Repr

abbrev servicesEnv (x : List ServiceTy) : Fields :=
  List.map (λ y => (y.name , Ltype.record y.args ⟶ y.res)) x

inductive Server : Schema → List ServiceTy → Type where
  | base : SchemaDef σ → Server σ []
  | addService : Server σ l → ServiceDef σ (toEnv (servicesEnv l)) t → Server σ (t :: l)
deriving Repr

syntax (priority := high) "#server" "[" term "]" "{" term,* "}" : term
macro_rules
  | `(#server[$z]{}) => `(Server.base $z)
  | `(#server[$z]{$x}) => `(Server.addService (Server.base $z) $x)
  | `(#server[$z]{$xs:term,*, $x}) => `(Server.addService #server[$z]{$xs,*} $x)

inductive AppPath where
  | root : AppPath

inductive Router : Env → List AppPath → Type where
  | nil : Router e []
  | cons : (p : AppPath) → Lexp e .node → Router e l → Router e (p :: l)

syntax (priority := high) "r[" term,* "]" : term
macro_rules
  | `(r[]) => `(Router.nil)
  | `(r[$x]) => `(let w := $x; Router.cons (w.fst) (w.snd) Router.nil)
  | `(l[$x, $xs:term,*]) => `(let w := $x; Router.cons (Prod.fst w) (Prod.snd w) r[$xs,*])

inductive ReactApp where
  | mk : Server σ γ → (paths : List AppPath) → Router react paths → ReactApp


syntax "#app" "[" term "]" "{" term,* "}" : term

macro_rules
  | `(#app [$z] { $[$x:term],* }) => `( ReactApp.mk $z [ $[Prod.fst $x],* ]  r[ $[$x],* ])
