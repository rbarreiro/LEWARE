import LEWARE.Html

inductive Form : Ltype → Type where
  | simpleString : Form Ltype.string

def formAttrs (α : Ltype) : Ltype :=
  .list (.sum [("defaultValue", α), ("onChange", α ⟶ .io .unit)])


def makeFormComponents [SubEnv browser e] (form : Form α)
        : Lexp e (formAttrs α ⟶ .node) :=
  func props =>
    match form with
      | .simpleString =>
          textInput @@
            (
              LFunctor.map @@
              (func p => lmatch (&p) lwith {
                || defaultValue x => cons(defaultValue, &x),
                || onChange x => cons(onChange, &x)
              }) @@
              &props
            )

def makeForm [SubEnv browser e] (f : Form α)
                  : Lexp e (formAttrs α ⟶ .node) :=
  func props =>
    widget @@
      (createSignal @@ findTag!(defaultValue, &props)) @@
      (func sig =>
        form @@
          l[ cons(onSubmit, .ldo
                    {
                      llet v <- .lastValue @@ &sig..value,
                      lmatch (&v) lwith{
                        || some x => (fromOption @@ (func x => .iopure @@ unit) @@ findTag!(onChange, &props)) @@ &x,
                        || none x => .iopure @@ unit
                      }
                    }
                  )
          ] @@
          l[
            makeFormComponents f @@
            (
              l[cons(onChange, func x => &sig..set @@ (some @@ &x))] +++?
              (LFunctor.map @@ (func x => cons(defaultValue, &x)) @@findTag!(defaultValue, &props))
            )
          ]
      )
