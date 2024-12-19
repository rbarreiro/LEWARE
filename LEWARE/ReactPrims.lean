import LEWARE.Basic

def findTagD (tag : String) (props : Lexp react e (.list (.sum ts))) (p : HasVar ts tag α) (d : Lexp react e α) : Lexp react e α :=
  sorry

macro "findTagD!(" t:ident "," x:term "," y:term ")" : term => `(findTagD $(Lean.quote (toString t.getId)) $x (by repeat constructor) $y)

def targetValue : Lexp react e (.event ⟶ .string) :=
  .prim [.declaration "targetValue" "const targetValue = x => x.target.value;"] "targetValue"

def preventDefault : Lexp react e (.event ⟶ .unit) :=
  .prim [.declaration "preventDefault" "const preventDefault = x => x.preventDefault()"] "preventDefault"

def text : Lexp react e (.string ⟶ .node) :=
  .prim [.declaration "text" "x => React.createElement('Fragment', null, x)"] "text"

def attr : Ltype := .tuple [.string, .sum [("stringAttr", .string), ("eventHandler", .event ⟶ .unit)]]

def node  (tag : String)
    : Lexp react e (.list attr ⟶ .list .node ⟶ .node) :=
  let name := s!"node_{tag}";
  .prim
    [
      .declaration
        "read_attrs"
        "const read_attrs = attrs => {let res = {};attrs.forEach(v => {res[v[0]] = v[1];}); return res};",
      .declaration
        name
        s!"const {name} = attrs => (children => React.createElement({tag}, read_attrs(attrs), children));",
    ]
    name

abbrev buttonProps : Ltype := .sum [
  ("text", .string),
  ("onClick", .unit ⟶ .unit)
]

def button : Lexp react e (.list buttonProps ⟶ .node)  :=
  func props =>
    node "button" @@
      (l[t2 @@ "type" @@ cons(stringAttr, "button")] +++ (flatMap @@
        (func p => lmatch (&p) lwith{
            || text x => l[],
            || onClick x => l[t2 @@ "onClick" @@ cons(eventHandler, func e => &x @@ unit)]
          }
        )
        @@ &props
      )) @@
      l[text @@ (findTagD!(text, &props, ""))]

def textInputProps : Ltype := .sum [
  ("onChange", .string ⟶ .unit),
  ("defaultValue", .string)
]

def textInput : Lexp react e (.list textInputProps ⟶ .node) :=
  func props =>
    node "input" @@
      (LFunctor.map @@
        (func p => lmatch(&p) lwith{
          || onChange x => t2 @@ "onChange" @@ cons(eventHandler, func e => &x @@ (targetValue @@ &e)),
          || defaultValue x => t2 @@ "defaultValue" @@ cons(stringAttr, &x)
        })
        @@ &props
      ) @@
      l[]

def formProps : Ltype := .sum [
  ("onSubmit", .unit ⟶ .unit),
]

def form : Lexp react e (.list formProps ⟶ .list .node ⟶ .node) :=
  func props, children =>
    node "form" @@
      (LFunctor.map @@
        (func p => lmatch(&p) lwith{
          || onSubmit x => t2 @@ "onSubmit" @@ cons(eventHandler, func e => llet z := preventDefault @@ &e ; &x @@ unit )
        }) @@
        &props
      ) @@
      &children

def widget (init : Lexp react e σ)
              (name : String)
                (body : Lexp react ([("props", .list (.sum ts)), ("state", σ), ("setState", σ ⟶ .unit)] ++ e) .node)
                  : Lexp react e (.list (.sum ts) ⟶ .node) :=
  .primWithExp2Decl
    []
    s!"Widget_{name}"
    (
      s!"function Widget_{name}" ++ "({props}){\n" ++
      " const [state, setState] = useState({arg1});\n" ++
      " return {arg2};\n" ++
      "}\n\n"
    )
    init
    body
    (s!"(props => React.createElement('Widget_{name}'" ++ ", {props: props}, []))")
