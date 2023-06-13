import Mathlib.ModelTheory.Syntax
import Incompleteness.Arithmetic

open FirstOrder
open FirstOrder.Language

namespace FirstOrder.Language

universe u v w u' v'

-- variable (L : FirstOrder.Language) (α : Type u') (n : ℕ)


inductive  QFFormula  {L : Language} {α : Type u'} {n : ℕ} : (L.BoundedFormula α n) →  Prop
  | falsum : QFFormula (falsum)
  | equal (t₁ t₂ : L.Term (Sum α (Fin n))) : QFFormula (equal)
  | rel (R : L.Relations l) (ts : Fin l → L.Term (Sum α (Fin n))) : QFFormula (rel)
  | imp {φ ψ} : QFFormula φ → QFFormula ψ → QFFormula (imp)

-- Test
example : Prop := by
  have L0 := FirstOrder.Language.empty
  have fs : (Formula L0 ℕ) := BoundedFormula.falsum
  have qf_fs := QFFormula (fs)
  
  have t0 : (Term L0 (ℕ ⊕ Fin 0)) := Language.Term.var (Sum.inl 0)
  have f0 : (Formula L0 ℕ) := BoundedFormula.equal t0 t0
  have qf_eq : (QFFormula f0) := by
    apply QFFormula.equal t0 t0

  -- have Larith := arithmetic

  exact True

#check BoundedFormula.rel
