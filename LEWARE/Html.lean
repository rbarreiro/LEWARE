import LEWARE.App

abbrev buttonProps : Ltype := .sum [
  ("text", .signal .string),
  ("onClick", .io .unit)
]

def button [SubEnv browser e] : Lexp e (.list buttonProps ⟶ .node)  :=
  func props =>
    node @@ "button" @@
      (l[.t2 @@ "type" @@ cons(stringAttr, "button")] +++ (flatMap @@
        (func p => lmatch (&p) lwith{
            || text x => l[],
            || onClick x => l[.t2 @@ "onClick" @@ cons(eventHandler, func e => &x)]
          }
        )
        @@ &props
      )) @@
      l[text @@ (fromOption @@ "" @@ findTag!(text, &props))]

def textInputProps : Ltype := .sum [
  ("onChange", .string ⟶ .io .unit),
  ("defaultValue", .string)
]

def textInput [SubEnv browser e] : Lexp e (.list textInputProps ⟶ .node) :=
  func props =>
    node @@ "input" @@
      (LFunctor.map @@
        (func p => lmatch(&p) lwith{
          || onChange x => .t2 @@ "onChange" @@ cons(eventHandler, func e => .ldo {
                                                                              llet z <- targetValue @@ &e,
                                                                              &x @@ &z
                                                  }),
          || defaultValue x => .t2 @@ "defaultValue" @@ cons(stringAttr, .signalpure @@ &x)
        })
        @@ &props
      ) @@
      l[]

def formProps : Ltype := .sum [
  ("onSubmit", .io .unit),
]

def form [SubEnv browser e] : Lexp e (.list formProps ⟶ .list .node ⟶ .node) :=
  func props, children =>
    node @@ "form" @@
      (LFunctor.map @@
        (func p => lmatch(&p) lwith{
          || onSubmit x => .t2 @@ "onSubmit" @@ cons(eventHandler, func e => .ldo {preventDefault @@ &e, &x})
        }) @@
        &props
      ) @@
      &children
