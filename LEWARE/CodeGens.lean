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

def genApp (app : ReactApp) : GeneratedApp :=
  match app with
    | .mk server _ router =>
        let migs := genMigrations server
        let client := ""
        { server := "server"
        , client := clientTemplate
                      (s!"<Router><Switch>{client}</Switch></Router>")
        , migrations := migs
        }

def escapeforRun (s : String) : String :=
  s.replace "\\\"" "\\\\\""

def deployApp (host : String) (port : Nat) (name : String) (app : ReactApp) : IO Unit :=
  do
    let a := genApp app
    let name_ := escapeString name |> escapeforRun
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
