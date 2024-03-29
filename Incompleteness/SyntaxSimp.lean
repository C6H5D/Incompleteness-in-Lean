import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Graph
import Incompleteness.Arithmetic
import Incompleteness.SigmaFormula

open FirstOrder
open FirstOrder.Language
open Arithmetic

namespace Arithmetic

-- auxillary lemmas that could be useful

theorem forall_distr_iff {α : Type} {P Q: α → Prop} : (∀ x, P x ↔ Q x) → ((∀ x, P x) ↔ (∀ x, P x)) := fun _ => OrderDual.forall

theorem exists_distr_iff {α : Type} {P Q: α → Prop} : (∀ x, P x ↔ Q x) → ((∃ y, P y) ↔ (∃ z, P z)) := fun _ => OrderDual.exists

-- simp helpers

@[simp high]
theorem realize_plus {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty ⊕ Fin n → ℕ} :
    (t₁ +' t₂).realize v = (t₁.realize v) + (t₂.realize v) := by apply Term.realize_functions_apply₂

@[simp high]
theorem realize_times {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty ⊕ Fin n → ℕ} :
    (t₁ *' t₂).realize v = (t₁.realize v) * (t₂.realize v) := by apply Term.realize_functions_apply₂

@[simp high]
theorem realize_le {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty → ℕ} :
    (t₁ ≤' t₂).Realize v xs ↔ (t₁.realize (Sum.elim v xs)) ≤ (t₂.realize (Sum.elim v xs)) := by apply BoundedFormula.realize_rel₂

@[simp high]
theorem realize_ne {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty → ℕ} :
    (t₁ ≠' t₂).Realize v xs ↔ (t₁.realize (Sum.elim v xs)) ≠ (t₂.realize (Sum.elim v xs)) := by simp only [BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, ne_eq]

@[simp high]
theorem realize_lt {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty → ℕ} :
    (t₁ <' t₂).Realize v xs ↔ (t₁.realize (Sum.elim v xs)) < (t₂.realize (Sum.elim v xs)) := by 
    change (((t₁ ≤' t₂) ⊓ (t₁ ≠' t₂)).Realize v xs) ↔ _
    rw [BoundedFormula.realize_inf]
    change ((t₁ ≤' t₂).Realize v xs) ∧ ((t₁ ≠' t₂).Realize v xs) ↔ _
    change (t₁.realize (Sum.elim v xs)) ≤ (t₂.realize (Sum.elim v xs)) ∧ (t₁.realize (Sum.elim v xs)) ≠ (t₂.realize (Sum.elim v xs)) ↔ _
    rw [lt_iff_le_and_ne]
    
@[simp high]
theorem realize_ge {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty → ℕ} :
    (t₁ ≥' t₂).Realize v xs ↔ (t₁.realize (Sum.elim v xs)) ≥ (t₂.realize (Sum.elim v xs)) := by rw [ge_iff_le]; rw [realize_le]

@[simp high]
theorem realize_gt {t₁ t₂ : BoundedArithmeticTerm n} {v : Empty → ℕ} :
    (t₁ >' t₂).Realize v xs ↔ (t₁.realize (Sum.elim v xs)) > (t₂.realize (Sum.elim v xs)) := by apply realize_lt

@[simp high]
theorem realize_succ {t: BoundedArithmeticTerm n} {v : Empty ⊕ Fin n → ℕ} :
    (succ' t).realize v = Nat.succ (t.realize v) := by apply Term.realize_functions_apply₁

@[simp high]
theorem realize_ofNat {l : ℕ} {v : Empty ⊕ Fin l → ℕ} :
    (ArithmeticTerm.ofNat n).realize v = n := by 
    induction' n with n IH
    trivial
    change (ArithmeticTerm.ofNat (n.succ)).realize v = n.succ
    change (succ' (ArithmeticTerm.ofNat n)).realize v = n.succ
    nth_rewrite 2 [← IH]
    apply realize_succ


@[simp↓]
theorem realize_ball_le {l : ℕ} {t: BoundedArithmeticTerm l.succ} {θ : BoundedArithmeticFormula l.succ} {v : Empty → ℕ} {xs : Fin l → ℕ} : (∀' x ≤' t, θ).Realize v xs ↔ ∀ a ≤ (t.realize (Sum.elim v (Fin.snoc xs a))), θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.realize_all]
  constructor <;> intro h a <;> specialize h a
  . rw [BoundedFormula.realize_imp, realize_le] at h
    intros
    apply h
    simpa
  . rw [BoundedFormula.realize_imp, realize_le]
    simpa

@[simp↓]
theorem realize_bex_le {l : ℕ} {t: BoundedArithmeticTerm l.succ} {θ : BoundedArithmeticFormula l.succ} {v : Empty → ℕ} {xs : Fin l → ℕ} : (∃' x ≤' t, θ).Realize v xs ↔ ∃ a ≤ (t.realize (Sum.elim v (Fin.snoc xs a))), θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.realize_ex]
  constructor <;> intro h <;> cases' h with a h <;> use a
  . rw [BoundedFormula.realize_inf, realize_le] at h
    intros
    constructor
    . cases' h with h _
      simp at h
      exact h
    . exact h.2
  . rw [BoundedFormula.realize_inf, realize_le]
    simpa

@[simp↓]
theorem realize_ball_lt {l : ℕ} {t: BoundedArithmeticTerm l.succ} {θ : BoundedArithmeticFormula l.succ} {v : Empty → ℕ} {xs : Fin l → ℕ} : (∀' x <' t, θ).Realize v xs ↔ ∀ a < (t.realize (Sum.elim v (Fin.snoc xs a))), θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.realize_all]
  constructor <;> intro h a <;> specialize h a
  . rw [BoundedFormula.realize_imp, realize_lt] at h
    intros
    apply h
    simpa
  . rw [BoundedFormula.realize_imp, realize_lt]
    simpa

@[simp↓]
theorem realize_bex_lt {l : ℕ} {t: BoundedArithmeticTerm l.succ} {θ : BoundedArithmeticFormula l.succ} {v : Empty → ℕ} {xs : Fin l → ℕ} : (∃' x <' t, θ).Realize v xs ↔ ∃ a < (t.realize (Sum.elim v (Fin.snoc xs a))), θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.realize_ex]
  constructor <;> intro h <;> cases' h with a h <;> use a
  . rw [BoundedFormula.realize_inf, realize_lt] at h
    intros
    constructor
    . cases' h with h _
      simp at h
      exact h
    . exact h.2
  . rw [BoundedFormula.realize_inf, realize_lt]
    simpa

@[simp]
theorem fin₃_0 {m n r : ℕ} : @Fin.snoc 2 (fun _ => ℕ) ![m, n] r 0 = m := rfl

@[simp]
theorem fin₃_1 {m n r : ℕ} : @Fin.snoc 2 (fun _ => ℕ) ![m, n] r 1 = n := rfl

@[simp]
theorem fin₃_2 {m n r : ℕ} : @Fin.snoc 2 (fun _ => ℕ) ![m, n] r 2 = r := rfl
-- @[simp]
-- theorem realize_var₃_0 : (&0 : BoundedArithmeticTerm 3).realize (Sum.elim (default : Empty → ℕ) (Fin.snoc ![m, n] r)) = m := by
--   simp
--   rfl

-- theorem tmp : Term.realize (Sum.elim (default : Empty → ℕ) (Fin.snoc ![m, n] r)) ((var ∘ Sum.inr) 0 : BoundedArithmeticTerm 3) = m := rfl

-- @[simp]
-- theorem realize_var₃_1 : (&1 : BoundedArithmeticTerm 3).realize (Sum.elim (default : Empty → ℕ) (Fin.snoc ![m, n] r)) = n := by
--   simp
--   rfl

-- @[simp]
-- theorem realize_var₃_2 : (&2 : BoundedArithmeticTerm 3).realize (Sum.elim (default : Empty → ℕ) (Fin.snoc ![m, n] r)) = r := by
--   simp
--   rfl

example (m n : ℕ) : (∃x : ℕ, x * x = m ∧ m = 0) ↔ ((∃' ((((&2) *' (&2)) =' (&0)) ⊓ (&0 =' (ArithmeticTerm.ofNat 0)))).Realize default ![m , n])  := by
  simp
  -- tauto

example (m n : ℕ) : (∃x ≤ n, x * x = m ∧ m = 0) ↔ ((∃' x ≤' &1, ((((&2) *' (&2)) =' (&0)) ⊓ (&0 =' (@ArithmeticTerm.ofNat 3 0)))).Realize default ![m , n])  := by
  simp only [realize_bex_le]
  simp
  -- apply exists_distr_iff
  -- have : ∀ (x : ℕ), x ≤ n ∧ x * x = m ∧ m = 0 ↔ x ≤ n ∧ x * x = m ∧ m = 0 := by simp only [forall_const]
  -- exact this

-- TODO: 0. if then else
-- 1. Automated Sigma_1 proof; 2. Prettier notation 3. better natural number coercion