import LEWARE.Basic
import LEWARE.ReactPrims

inductive Form : Ltype → Type where
  | simpleString : Form Ltype.string
--  | custom : ((Lexp react e (.option α) → Lexp react e .unit) → Lexp react e .node) → Form α

def makeFormComponents
      (form : Form α)
        (start : Lexp react e (.option α))
          (onchange : Lexp react e (.option α) → Lexp react e .unit)
            : Lexp react e .node :=
  match form with
    | .simpleString => sorry

def makeForm (form : Form α)
               (onsubmit : Lexp react e (.option α) → Lexp react e .unit)
                  : Lexp react e .node :=
  sorry
