import LEWARE.Basic


def text (x : Lexp react e .string)  : Lexp react e .node :=
  .prim1 [] "React.createElement('Fragment', null, {arg0})" x

def node  (tag : Lexp react e .string)
          (attrs : Lexp react e (.list (.tuple [.string, .string])))
          (eventHandlers : Lexp react e (.list (.tuple [.string, .event ⟶ .unit])))
          (children : Lexp react e (.list .node))
            : Lexp react e .node :=
  .prim4 [] "React.createElement({arg0}, Object.fromEntries{arg1.concat({arg2})}, {arg3})" tag attrs eventHandlers children

def buttonProps : Ltype := .sum [
  ("text", .string),
  ("onclick", .unit)
]

def button (props : Lexp react e (.list buttonProps)) : Lexp react e .node  :=
  node
    "body"
    l[]
    l[t2 "onClick" (.lambda "_" (fromOption (unit) (.relax (findTag! "onclick" in props))))]
    l[text (fromOption "" (findTag! "text" in props))]
