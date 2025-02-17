import LEWARE.Basic
import Lean.Data.Json

open Lean
open Json

def attr : Ltype := .tuple [.string, .sum [("stringAttr", .signal .string), ("eventHandler", .event ⟶ .io .unit)]]


abbrev insertResTy := Ltype.record [("inserted", .nat)]

abbrev browser : Env :=
  [ ("node", .base (.string ⟶ .list attr ⟶ .list .node ⟶ .node))
  , ("text", .base (.signal .string ⟶ .node))
  , ("targetValue", .base (.event ⟶ .io .string))
  , ("preventDefault", .base (.event ⟶ .io .unit))
  , ("widgetWithDestroy", .parametric (λ α => .io α ⟶ (α ⟶ .node) ⟶ (α ⟶ .io .unit) ⟶ .node))
  , ("createSignal", .parametric (λ α => α ⟶ .io (.record [("set", α ⟶ .io .unit), ("value", .signal α)])))
  ]

def node [se : SubEnv browser e] : Lexp e (.string ⟶ .list attr ⟶ .list .node ⟶ .node) :=
  let p : HasVar browser "node" (.string ⟶ .list attr ⟶ .list .node ⟶ .node) := by repeat constructor
  Lexp.var "node" (se.adaptVar p)

def text [se : SubEnv browser e] : Lexp e (.signal .string ⟶ .node) :=
  let p : HasVar browser "text" (.signal .string ⟶ .node) := by repeat constructor
  Lexp.var "text" (se.adaptVar p)

def targetValue [se : SubEnv browser e] : Lexp e (.event ⟶ .io .string) :=
  let p : HasVar browser "targetValue" (.event ⟶ .io .string) := by repeat constructor
  Lexp.var "targetValue" (se.adaptVar p)

def preventDefault [se : SubEnv browser e] : Lexp e (.event ⟶ .io .unit) :=
  let p : HasVar browser "preventDefault" (.event ⟶ .io .unit) := by repeat constructor
  Lexp.var "preventDefault" (se.adaptVar p)

def widget [se : SubEnv browser e] : Lexp e (.io α ⟶ (α ⟶ .node) ⟶ .node) :=
  let p : HasGenVar browser "widgetWithDestroy" (.parametric (λ α => .io α ⟶ (α ⟶ .node) ⟶ (α ⟶ .io .unit) ⟶ .node)) :=
            by repeat constructor
  let w : Lexp e (.io α ⟶ (α ⟶ .node) ⟶ (α ⟶ .io .unit) ⟶ .node) :=
            Lexp.parametricVar "widgetWithDestroy" α (se.adaptVar p)
  func setup, render =>  (.relax (.relax w)) @@ &setup @@ &render @@ (func x => .iopure @@ unit)

def createSignal [se : SubEnv browser e] : Lexp e (α ⟶ .io (.record [("set", α ⟶ .io .unit), ("value", .signal α)])) :=
  let p : HasGenVar browser "createSignal"
    (.parametric (λ α => α ⟶ .io (.record [("set", α ⟶ .io .unit), ("value", .signal α)]))) :=
            by repeat constructor
  let w : Lexp e (α ⟶ .io (.record [("set", α ⟶ .io .unit), ("value", .signal α)])) :=
            Lexp.parametricVar "createSignal" α (se.adaptVar p)
  w

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
deriving Repr, ToJson

structure ServiceTy where
  name : String
  args : Fields
  res : Ltype
  roles : AccessPolicy
deriving Repr, ToJson


inductive ServiceDef : Schema → Env → ServiceTy → Type where
  | service : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ e ++ serviceEnv) (.io α.res) →
                  ServiceDef σ e α
  | dbService : (α : ServiceTy) →
                Lexp (toEnv α.args ++ toEnv (schemaEnv σ) ++ e ++ dbServiceEnv) (.io α.res) →
                  ServiceDef σ e α
deriving Repr

instance : ToJson (ServiceDef σ e α) where
  toJson
    | ServiceDef.service α e => toJson [Json.str "service", toJson α, toJson e]
    | ServiceDef.dbService α e => toJson [Json.str "dbService", toJson α, toJson e]

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

inductive ReactApp where
  | mk : Server σ γ → Lexp browser .node → ReactApp

macro "#app" "[" s:term "]" "{" n:term "}" : term => `(ReactApp.mk $s $n)
