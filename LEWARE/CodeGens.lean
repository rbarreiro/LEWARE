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

def runtime : String :=
  "
    function lexp_istreampure(x) {
      return (callback => callback(x));
    }

    function text(x) {
      return Imutable.Map({k: \"text\", v: x});
    }

    function makeNode(x){
      switch(x.get(k)){
        case \"text\":
          const n = document.createTextNode(\"\");
          x.get(v)((y) => n.nodeValue = y);
          return n
        default:
          throw \"Invalid node\";
      }
    }
  "

def clientTemplate (client : String) : String :=
  "
  <!DOCTYPE html>
  <html>
  <body>
    <div id=\"root\"></div>
    <script src=\"https://cdnjs.cloudflare.com/ajax/libs/immutable/5.0.3/immutable.min.js\"
            integrity=\"sha512-7gKzXmjcoHpm+sl09bSCRqlj8XlxpyNhjny1jur6yyqQ6Tiw6q/loRThw10PcTYnjiWeNJZOpshsbCSJT9TLYA==\"
            crossorigin=\"anonymous\"
            referrerpolicy=\"no-referrer\">
    </script>
    <script>" ++ runtime ++ "\n\n" ++
      "const mainNode =" ++ client ++ ";
      document.body.appendChild(makeNode(mainNode));
    </script>
  </body>
  </html>
  "

mutual
  def genJSMatch : LMatch e ts β → String
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
    | .istreampure =>
      "lexp_istreampure"
    | .findTag tag props _ default =>
        let props_ := genJS props
        let default_ := genJS default
        s!"lexp_findTag({escapeString tag}, {props_}, {default_})"
end

def genApp (app : ReactApp) : GeneratedApp :=
  match app with
    | .mk server page =>
        let migs := genMigrations server
        let client := genJS page
        { server := toJson (genServices server) |>.pretty
        , client := clientTemplate client
        , migrations := migs
        }

def escapeforRun (s : String) : String :=
  s.replace "\\\"" "\\\\\""

def appName (app : ReactApp) : String :=
  match app with
    | .mk server _ =>
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
