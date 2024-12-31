import LEWARE.Basic


structure GeneratedApp where
  server : String
  client : String
deriving Repr

structure ToJsState where
  declarations : List String
  usedNames : List String
  uid : Nat
deriving Repr

def initS : ToJsState :=
  { declarations := []
  , usedNames := []
  , uid := 0
  }

def escapeString (s : String) : String :=
  let f := λ s c => match c with
                      | '\\' => s ++ "\\\\"
                      | '\n' => s ++ "\\n"
                      | '"' => s ++ "\\\""
                      | o => s ++ o.toString;
   "\"" ++ String.foldl f "" s ++ "\""

abbrev CodeGen (x : Type) : Type := StateT ToJsState (Except String) x

def uid : CodeGen Nat :=
  modifyGet (λ s => (s.uid + 1, {s with uid := s.uid + 1}))

def mkName : CodeGen String :=
  ("lvar" ++ toString .) <$> uid

def addDep : Dependency → CodeGen Unit
  | .declaration n x =>
    do
      let s ← get
      if s.declarations.contains x && s.usedNames.contains n then pure ()
        else if s.usedNames.contains n then MonadExcept.throw s!"{n} used in more than one definition"
          else set {s with usedNames := n :: s.usedNames, declarations := x :: s.declarations}

def addDeps : List Dependency → CodeGen Unit
  | (x :: xs) =>
    do
      addDep x
      addDeps xs
  | [] =>
    return .unit

mutual

  def matchToJS (val :String) (m : LMatch (.js v) e ts β) : CodeGen String :=
    match m with
    | .matchnil =>
      return "undefined"
    | .matchcons rs n v x =>
      do
        let x_ ← toJS x
        let rs_ ← matchToJS val rs
        return s!"{val}.hasOwnProperty({n}) ? ({v} => {x_})({val}[{n}]) : ({rs_})"

  def toJS : (e : Lexp (.js v) e α) → CodeGen String
    | .lit l =>
      match l with
        | .str s => return (escapeString s)
    | .llet n v b =>
      do
        let v_ <- toJS v
        let b_ <- toJS b
        return s!"({n} => {b_})({v_})"
    | .var n _ =>
      return n
    | .app f x =>
      do
        let f_ <- toJS f
        let x_ <- toJS x
        return s!"{f_}({x_})"
    | .relax z =>
      toJS z
    | .listnil =>
      return "Immutable.List()"
    | .listcons =>
      do
        addDeps [.declaration "listcons" "const listcons= x => (y => y.unshift(x));"]
        return s!"listcons"
    | .recordnil =>
      return "Immutable.Map()"
    | .recordcons n x xs =>
      do
        let x_ <- toJS x
        let xs_ <- toJS xs
        return s!"{xs_}.set({n}, {x_})"
    | .mk k v _ =>
      do
        let v_ <- toJS v
        return  "{" ++ s!"{k}: {v_}" ++ "}"
    | .lambda n b =>
      do
        let b_ <- toJS b
        return s!"function({n})" ++ "{" ++ s!"return {b_}" ++ "}"
    | .lmatch x m =>
      do
        let x_ ← toJS x
        let n ← mkName
        let m_ ← matchToJS n m
        return s!"({n} => {m_})({x_})"
    | .prim deps d =>
      do
        addDeps deps
        return d
    | .primWithExp2Decl deps n t x y d =>
      do
        let x_ ← toJS x
        let y_ ← toJS y
        let repl : String → String := λ x => (x.replace "{arg1}" x_).replace "{arg2}" y_
        addDeps (.declaration (repl n) (repl t) :: deps)
        return repl d
end

mutual
  def matchToRethink (val :String) (m : LMatch .rethinkdb e ts β) : CodeGen (List String) :=
    match m with
    | .matchnil =>
      return []
    | .matchcons rs n v x =>
      do
        let x_ ← toRethink x
        let rs_ ← matchToRethink val rs
        return s!"{val}.hasFields({n}), {val}.getField({n}).do({v} => {x_})" :: rs_

  def toRethink : (e : Lexp .rethinkdb e α) → CodeGen String
    | .lit l =>
      match l with
        | .str s => return s!"r.expr({escapeString s})"
    | .llet n v b =>
      do
        let v_ <- toRethink v
        let b_ <- toRethink b
        return s!"{v_}.do(({n} => ({b_})))"
    | .var n _ =>
      return n
    | .app f x =>
      do
        let f_ <- toRethink f
        let x_ <- toRethink x
        return s!"{f_}({x_})"
    | .relax x =>
      toRethink x
    | .listnil =>
      return "r.expr([])"
    | .listcons =>
      do
        addDeps [.declaration "r_listcons" "const r_listcons= x => (y => y.insertAt(0, x));"]
        return s!"r_listcons"
    | .recordnil =>
      return "r.expr({})"
    | .recordcons n x xs =>
      do
        let x_ <- toRethink x
        let xs_ <- toRethink xs
        return s!"{xs_}.coerceTo('array').append([{n}, {x_}]).coerceTo('object')"
    | .mk k v _ =>
      do
        let v_ <- toRethink v
        return  s!"r.object({k}, {v_})"
    | .lambda n b =>
      do
        let b_ <- toRethink b
        return s!"function({n})" ++ "{" ++ s!"return {b_}" ++ "}"
    | .lmatch x m =>
      do
        let x_ ← toRethink x
        let n ← mkName
        let m_ ← matchToRethink n m
        let bs := String.intercalate ", " m_
        return s!"({n} => r.branch({bs}))({x_})"
    | .prim deps d =>
      do
        addDeps deps
        return d
    | .primWithExp2Decl deps n t x y d =>
      do
        let x_ ← toRethink x
        let y_ ← toRethink y
        let repl : String → String := λ x => (x.replace "{arg1}" x_).replace "{arg2}" y_
        addDeps (.declaration (repl n) (repl t) :: deps)
        return repl d
end


def genInitDB (schemaName : String) (sch : Schema) : Lexp .rethinkdb [] .unit :=
  llet x := dbCreate @@ "leware";
  llet y := dbCreate @@ (.lit (.str schemaName));
  llet z := sch.foldl (λ e (n, _, _) => llet w := tableCreate @@ (.lit (.str schemaName)) @@ (.lit (.str n)) ; .relax e) unit;
  unit

def genSchemaMigrationQuery (schemaDef : SchemaDef σ) : Lexp .rethinkdb [] .unit :=
  match schemaDef with
    | .new name sch =>
      (elem @@ "leware" @@ dbList) ?? unit :
        genInitDB name sch

def genSchemaMigration (schemaDef : SchemaDef σ) : CodeGen String :=
  do
    let q : Lexp .rethinkdb [] .unit := genSchemaMigrationQuery schemaDef
    let qs <- toRethink q
    return s!"{qs}.run(connection, function(err, result)\{console.log(err, result)})"

def genServer (server : Server sch srvs) : CodeGen String :=
  do
    let z ← match server with
              | .addService rest service =>
                do
                  let rest_ <- genServer rest
                  return rest_
              | .base schema =>
                genSchemaMigration schema
    return "" ++ z

def genPath : AppPath → CodeGen String
  | .root =>
    return "/"

def genClient : Router e p → CodeGen String
  | .nil =>
    return ""
  | .cons p x xs =>
    do
      let x_ <-  toJS x
      let p_ <-  genPath p
      let xs_ <- genClient xs
      return s!"(<Route path=\"{p_}\">{x_}\n</Route>{xs_})"

def clientTemplate (declarations : String) (client : String) : String :=
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
  import { createRoot } from 'react-dom/client';
  "++ declarations ++ "\n\n" ++
  "
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

def genApp (app : ReactApp) : Except String GeneratedApp :=
  match app with
    | .mk server _ router =>
      match (genServer server).run initS with
        | .ok x =>
          match (genClient router).run initS with
            | .ok y => .ok { server := (String.intercalate "\n" x.snd.declarations) ++ "\n\n" ++ x.fst
                           , client := clientTemplate
                                          (String.intercalate "\n" y.snd.declarations)
                                          (s!"<Router><Switch>{y.fst}</Switch></Router>")
                           }
            | .error y => .error y
        | .error x => .error x

def deployApp (host : String) (port : Nat) (name : String) (app : ReactApp) : IO Unit :=
  match genApp app with
    | .ok a =>
      do
        let payload := "{" ++ s!"\"id\" : {escapeString name}, \"server\" : {escapeString a.server},\"page\" : {escapeString a.client}," ++ "}"
        let url := s!"http://{host}:{toString port}/upsertapp"
        let output ← IO.Process.run { cmd := "curl.exe", args:= #["-X", "POST", "-d", payload, url] }
        IO.println output
    | .error x =>
      IO.println x
