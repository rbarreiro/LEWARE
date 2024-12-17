import LEWARE.Basic


structure GeneratedApp where
  server : String
  client : String
deriving Repr

structure ToJsState where
  declarations : List String
  usedNames : List String
deriving Repr

def initS : ToJsState :=
  { declarations := []
  , usedNames := []
  }

def escape_string (s : String) : String :=
  let f := λ s c => match c with
                      | '\\' => s ++ "\\\\"
                      | '\n' => s ++ "\\n"
                      | '"' => s ++ "\\\""
                      | o => s ++ o.toString;
   "\"" ++ String.foldl f "" s ++ "\""

abbrev CodeGen (x : Type) : Type := StateT ToJsState (Except String) x

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

  def toJSRecordLit (e : Lexp (.js v) e α) : CodeGen (Option (List String)) :=
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

  def matchToJS : LMatch (.js v) e ts β → CodeGen String
    | .matchnil =>
      return ""
    | .matchcons rs n v x =>
      do
        let x_ <- toJS x
        sorry

  def toJS : (e : Lexp (.js v) e α) → CodeGen String
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
    | .prim deps d =>
      do
        addDeps deps
        return d
    | .primWithExp2Decl deps n t x y d =>
      sorry
end

mutual
  def toRethinkRecordLit (e : Lexp .rethinkdb e α) : CodeGen (Option (List String)) :=
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

  def matchToRethink : LMatch (.js v) e ts β → CodeGen String
    | .matchnil =>
      return ""
    | .matchcons rs n v x =>
      do
        let x_ <- toJS x
        sorry

  def toRethink : (e : Lexp .rethinkdb e α) → CodeGen String
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
    | .prim deps d =>
      do
        addDeps deps
        return d
    | .primWithExp2Decl deps n t x y d =>
      sorry
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
    return s!"{qs}.run(connection, function(err, result)\{})"

def genServer (server : Server sch srvs) : CodeGen String :=
  match server with
    | .addService rest service =>
      do
        let rest_ <- genServer rest
        return rest_
    | .base schema =>
      genSchemaMigration schema

def genApp_ (app : ReactApp) : CodeGen GeneratedApp :=
  match app with
    | .mk server paths router =>
      do
        let server_ <- genServer server
        return {server := "", client := ""}


def genApp (app : ReactApp) : Except String GeneratedApp :=
  match (genApp_ app).run initS with
    | .ok x => .ok x.fst
    | .error x => .error x

/-
def genReactDef : ReactDef servs e name fs β → CodeGen String
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

def genReactApp : ReactApp servs e → CodeGen String
  | .appnil _ =>
    return ""
  | .appcons x y =>
    do
      let x_ <- genReactApp x
      let y_ <- genReactDef y
      return x_ ++ "\n\n" ++ y_
-/
