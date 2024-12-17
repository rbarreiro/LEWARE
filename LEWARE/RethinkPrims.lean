import LEWARE.Basic

abbrev InsertResTy := Ltype.record [("inserted", .nat)]

def insertIdValue : Lexp .rethinkdb e (.table i v ⟶ i ⟶ v ⟶ InsertResTy) :=
  .prim
    [.declaration "r_insert_id_value" "const r_insert_id_value = tbl => (i => (v=> tbl.insert({id: i, value: v})));"]
    "r_insert_id_value"

def uuid : Lexp .rethinkdb e (.string) :=
  .prim [] "r.uuid()"

def now : Lexp .rethinkdb e (.datetime) :=
  .prim [] "r.now()"
