import Mathlib.ModelTheory.Syntax
open FirstOrder
open FirstOrder.Language


universe u v w u' v'

variable (L : FirstOrder.Language) (α : Type u') (n : ℕ)

#check (BoundedFormula.imp)


inductive  QFFormula : (L.BoundedFormula α n) →  Prop
  | falsum : QFFormula (falsum)
  | equal (t₁ t₂ : L.Term (Sum α (Fin n))) : QFFormula (equal)
  | rel (R : L.Relations l) (ts : Fin l → L.Term (Sum α (Fin n))) : QFFormula (rel)
  | imp {φ ψ} : QFFormula φ → QFFormula ψ → QFFormula (imp)

-- Test
example : Prop := by
  have L0 := FirstOrder.Language.empty
  have t0 : (Language.Term L0 ℕ) := Language.Term.var 0
  -- have phi: (Formula) := L0.BoundedFormula.falsum 0

  -- have : QFFormula ((L0.BoundedFormula α 0).falsum)

  exact True

  #check Language