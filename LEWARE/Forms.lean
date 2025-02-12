import LEWARE.Html

inductive Form : Ltype → Type where
  | simpleString : Form Ltype.string

def formComponentAttrs (α : Ltype) : Ltype :=
  .list (.sum [("defaultValue", α), ("onChange", α ⟶ .io .unit)])

/-
def makeFormComponents
    [SubEnv react e]
      (form : Form α)
        : Lexp e (formComponentAttrs α ⟶ .node) :=
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

def formAttrs (α : Ltype) : Ltype :=
  .list (.sum [("defaultValue", α), ("onSubmit", option α ⟶ .unit)])
-/
/-
def makeForm (form : Form α)
                  : Lexp react e (formAttrs α ⟶ .node) :=
  func props =>
    sorry
-/
