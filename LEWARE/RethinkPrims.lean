import LEWARE.Basic

abbrev InsertResTy := Ltype.record [("inserted", .nat)]

def insertIdValue (tbl : Lexp .rethinkdb e (.table i v))
    (id : Lexp .rethinkdb e i)
      (value : Lexp .rethinkdb e v)
        : Lexp .rethinkdb e InsertResTy :=
  .prim3 [] "{arg0}.insert({id: {arg1}, value: {arg2}})" tbl id value

def uuid : Lexp .rethinkdb e (.string) :=
  .prim0 [] "r.uuid()"

def now : Lexp .rethinkdb e (.datetime) :=
  .prim0 [] "r.now()"
