import LEWARE.App

open Lean
open Json

structure GeneratedApp where
  server : String
  client : String
  migrations : List String
deriving Repr

def escapeString (s : String) : String :=
  let f := λ s c => match c with
                      | '\\' => s ++ "\\\\"
                      | '\n' => s ++ "\\n"
                      | '"' => s ++ "\\\""
                      | o => s ++ o.toString;
   "\"" ++ String.foldl f "" s ++ "\""

def getServerSchema (server : Server sch srvs) : SchemaDef sch :=
  match server with
    | .addService rest service =>
      getServerSchema rest
    | .base sch =>
      sch

abbrev migrationEnv : Env :=
  [ ("tableCreate", .base (.string ⟶ .string ⟶ .io .unit))
  ]

def genStartMigration  (name : String)  (sch : Schema) : Lexp migrationEnv (.io .unit) :=
  match sch with
    | [] =>
      .iopure @@ unit
    | (n, _, _) :: xs =>
      .ldo {
        &tableCreate @@ (.lit (.str ("app_" ++ name))) @@ (.lit (.str n)),
        genStartMigration name xs
      }

/-
def genInitDB (schemaName : String) (sch : Schema) : Lexp .rethinkdb [] .unit :=
  llet z := sch.foldl (λ e (n, _, _) => llet w := tableCreate @@ (.lit (.str schemaName)) @@ (.lit (.str n)) ; .relax e) unit;
  unit
-/
  --let q := genInitDB ("app_" ++ name) sch

--  match (toRethink q).run initS with
--    | .ok x => .ok ("(function(){" ++ (String.intercalate "\n" x.snd.declarations) ++ "\n\nreturn " ++ x.fst ++ "})")
--    | .error x => .error x

def genMigrations_ (schDef : SchemaDef sch) : List String :=
  match schDef with
    | .new name sch =>
      [genStartMigration name sch |> toJson |>.pretty]

def genMigrations (server : Server sch srvs) : List String :=
  genMigrations_ (getServerSchema server)

def genServices (server : Server sch srvs) : List Json :=
  match server with
    | .addService rest service =>
      genServices rest ++ [toJson service]
    | .base _ =>
      []

/-
def genService (service : ServiceDef sch env srv) : CodeGen String :=
  match service with
    | .service _ x =>
      do
        let x_ <- toJS x
        return x_
    | .dbService _ x =>
      do
        let x_ <- toRethink x
        return x_

def genServer (server : Server sch srvs) : CodeGen String :=
  match server with
    | .addService rest service =>
      do
        let rest_ <- genServer rest
        let service_ <- genService service
        return rest_ ++ "\n\n" ++ service_
    | .base _ =>
      return "{}"
-/
def genPath : AppPath → String
  | .root =>
      "/"

/-
def genClient : Router e p → CodeGen String
  | .nil =>
    return ""
  | .cons p x xs =>
    do
      let x_ <-  toJS x
      let p_ <-  genPath p
      let xs_ <- genClient xs
      return s!"(<Route path=\"{p_}\">{x_}\n</Route>{xs_})"
-/

def clientTemplate (client : String) : String :=
  "
  <!DOCTYPE html>
  <html>
  <body>
    <div id=\"root\"></div>
  </body>
  <!-- This setup is not suitable for production. -->
  <!-- Only use it in development! -->
  <script src=\"https://unpkg.com/@babel/standalone/babel.min.js\"></script>
  <script async src=\"https://ga.jspm.io/npm:es-module-shims@1.7.0/dist/es-module-shims.js\"></script>
  <script type=\"importmap\">
  {
    \"imports\": {
      \"react\": \"https://esm.sh/react?dev\",
      \"react-dom/client\": \"https://esm.sh/react-dom/client?dev\"
    }
  }
  </script>
  <script src=\"https://cdn.jsdelivr.net/npm/immutable@5.0.3/dist/immutable.min.js\"></script>
  <script type=\"text/babel\" data-type=\"module\">
  import React, { StrictMode } from 'react';
  import { createRoot } from 'react-dom/client';\n

  let App = function MyApp() {
    return (" ++ client ++
    "
    );
  }


  const root = createRoot(document.getElementById('root'));
  root.render(
    <StrictMode>
      <App />
    </StrictMode>
  );
  </script>

  </html>
  "
/-
structure ToJsState where
  uid : Nat

def initS : ToJsState :=
  { uid := 0
  }

abbrev CodeGen (x : Type) : Type := StateM ToJsState x

def uid : CodeGen Nat :=
  modifyGet (λ s => (s.uid + 1, {s with uid := s.uid + 1}))

def mkName : CodeGen String :=
  ("lvar" ++ toString .) <$> uid
-/

mutual
  def genJSMatch : LMatch e ts β →String
    | LMatch.matchnil => "Immutable.Map()"
    | LMatch.matchcons m n v b =>
        let b_ := genJS b
        let m_ := genJSMatch m
        s!"{m_}.set(\"{n}\", {v} => {b_})"

  def genJSDo : Ldo e α → String
    | Ldo.base x => genJS x
    | Ldo.bind n v x =>
      let v_ := genJS v
      let x_ := genJSDo x
      s!"ldo_bind({v_}, {n} => {x_})"
    | Ldo.seq x y =>
      let x_ := genJS x
      let y_ := genJSDo y
      s!"ldo_seq({x_}, {y_})"


  def genJS : Lexp e α → String
    | .lit (Lit.str s) => (escapeString s)
    | .lit Lit.unit => "null"
    | .llet n v b =>
        let v_ := genJS v
        let b_ := genJS b
        s!"({n} => {b_})({v_})"
    | .var n _ => n
    | Lexp.parametricVar n _ _ => n
    | Lexp.parametric2Var n _ _ _ => n
    | .listnil => "Immutable.List()"
    | .ldo x => genJSDo x
    | .relax x => genJS x
    | .app f x =>
        let f_ := genJS f
        let x_ := genJS x
        s!"{f_}({x_})"
    | .recordnil => "Immutable.Map()"
    | .recordcons n x xs =>
        let x_ := genJS x
        let xs_ := genJS xs
        s!"{xs_}.set(\"{n}\", {x_})"
    | .mk n x _ =>
        let x_ := genJS x
        "{" ++ s!"k : {escapeString n}, v: {x_}" ++ "}"
    | .lambda n b =>
        let b_ := genJS b
        s!"({n}) => {b_}"
    | .lmatch x m =>
        let x_ := genJS x
        let m_ := genJSMatch m
        s!"((m, x) => m.get(x.k)(x.v))({m_})({x_})"
    | .listcons =>
      "lexp_listcons"
    | .branch =>
      "lexp_branch"
    | .t2 =>
      "lexp_t2"
    | .strEq =>
      "lexp_strEq"
    | .listAppend =>
      "lexp_listAppend"
    | .listMap =>
      "lexp_listMap"
    | .elem =>
      "lexp_elem"
    | .foldl =>
      "lexp_foldl"
    | .iopure =>
      "lexp_iopure"
    | .findTag tag props _ default =>
        let props_ := genJS props
        let default_ := genJS default
        s!"lexp_findTag({escapeString tag}, {props_}, {default_})"
end


def genRouter : Router e p → String
  | .nil => ""
  | .cons p x xs =>
      let x_ := genJS x
      let p_ := genPath p
      let xs_ := genRouter xs
      s!"<Route path=\"{p_}\">{x_}</Route>{xs_}"

def genApp (app : ReactApp) : GeneratedApp :=
  match app with
    | .mk server _ router =>
        let migs := genMigrations server
        let client := genRouter router
        { server := toJson (genServices server) |>.pretty
        , client := clientTemplate
                      (s!"<Router><Switch>{client}</Switch></Router>")
        , migrations := migs
        }

def escapeforRun (s : String) : String :=
  s.replace "\\\"" "\\\\\""

def appName (app : ReactApp) : String :=
  match app with
    | .mk server _ _ =>
      match getServerSchema server with
        | .new name _ => name


def deployApp (host : String) (port : Nat) (app : ReactApp) : IO Unit :=
  do
    let a := genApp app
    let name_ := escapeString (appName app) |> escapeforRun
    let server_ := escapeString a.server |> escapeforRun
    let client_ := escapeString a.client |> escapeforRun
    let migrations_ := "[" ++ String.intercalate "," (a.migrations.map (λ x => escapeString x |> escapeforRun)) ++ "]"
    let payload := "{" ++
                    s!"\"id\" : {name_}, \"server\" : {server_},\"page\" : {client_}, \"migrations\" : {migrations_}" ++
                    "}"
    IO.println payload
    let url := s!"http://{host}:{toString port}/upsertapp"
    let output ← IO.Process.run {
      cmd := "curl.exe",
      args:= #[ "-X", "POST"
              , "-H", "accept: application/json"
              , "-H", "Content-Type: application/json"
              ,"-d", payload
              , url
              ]
    }
    IO.println output
