import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Computability.PartrecCode
import Incompleteness.Arithmetic
import Incompleteness.SigmaFormula
import Incompleteness.SyntaxSimp

namespace FirstOrder
namespace Language
namespace Arithmetic

open BoundedFormula
open Arithmetic

def x0 : BoundedArithmeticTerm 2 := &0
def x1 : BoundedArithmeticTerm 2 := &1
def y0 : BoundedArithmeticTerm 3 := &0
def y1 : BoundedArithmeticTerm 3 := &1
def y2 : BoundedArithmeticTerm 3 := &2
-- def q0 : BoundedArithmeticFormula 1 := (x0 =' x0)
-- def pq : ArithmeticFormula := ∃' q0
-- variable (φ : BoundedFormula L_arithmetic ℕ 2)
def φ : BoundedArithmeticFormula 2 := x0 =' x1
def ψ₀ : BoundedArithmeticFormula 2 := ArithmeticTerm.ofNat 0 =' x1
def ψ_succ  : BoundedArithmeticFormula 2 := succ' x0 =' x1
def ψ_left : BoundedArithmeticFormula 2 := ∃' (((y2 <' y0) ⊓ (((y0 ⬝' y0) +' y2) =' y1)) ⊔ ((y0 ≤' y2) ⊓ (((y2 ⬝' y2) +' y2 +' y0) =' y1)))

-- @[simp] theorem Part.get_pure 

-- @[simp] lemma mylem : _ = _ := rfl

theorem part_rec_implies_sigma_one_definable {f : ℕ →. ℕ} {hf : Nat.Partrec f} :
        ∃ φ : BoundedFormula L_arithmetic Empty 2, (IsSigma1 φ) ∧ ∀ m n : ℕ, φ.Realize default ![m, n] ↔ (f m = Part.some n) := by
    induction hf with
    | zero => 
        use ψ₀
        constructor
        . apply IsSigma1.of_isDelta0 
          apply IsDelta0.of_isQF
          apply BoundedFormula.IsQF.of_isAtomic
          apply BoundedFormula.IsAtomic.equal
        . intro m n
          rw [ψ₀, x1]
          symm
          exact PartENat.natCast_inj
    | succ => 
        use ψ_succ
        constructor
        . apply IsSigma1.of_isDelta0 
          apply IsDelta0.of_isQF
          apply BoundedFormula.IsQF.of_isAtomic
          apply BoundedFormula.IsAtomic.equal
        . intro m n
          rw [ψ_succ, x0, x1]
          symm
          exact PartENat.natCast_inj
    | left => 
        -- use ψ_left
        use ∃' (((&1 <' &2) ⊓ (((&2 ⬝' &2) +' &1) =' &0)) ⊔ ((&2 ≤' &1) ⊓ (((&1 ⬝' &1) +' &1 +' &2) =' &0)))
        constructor
        . apply IsSigma1.ex
          apply IsSigma1.of_isDelta0
          apply IsDelta0.or <;> apply IsDelta0.and

          apply IsDelta0.and
          case left.left.h.h.h1.h1.h2 =>
            change IsDelta0 (∼(_ =' _))
            apply IsDelta0.of_isQF
            apply IsQF.imp 
            apply IsQF.of_isAtomic
            apply IsAtomic.equal
            apply IsQF.falsum

          all_goals
            apply IsDelta0.of_isQF; apply IsQF.of_isAtomic
          
          apply IsAtomic.rel
          apply IsAtomic.equal
          apply IsAtomic.rel
          apply IsAtomic.equal

        . intro m n
          suffices : (∃ r, Nat.pair n r = m) ↔ (@PFun.lift ℕ ℕ (fun n => (Nat.unpair n).fst) m = Part.some n)
          . rw [← this]
            simp
            unfold Nat.pair
            change (∃ a, _) ↔ (∃ b, _)
            constructor <;> intro h <;> cases' h with x h <;> use x
            . cases' (em (n < x)) with hl hr
              . rw [if_pos hl]
                simp [hl] at h
                cases' h with tmp1 tmp2
                . exact tmp1
                . linarith
              . rw [if_neg hr]
                tauto
            . cases' (em (n < x)) with hl hr
              . rw [if_pos hl] at h
                left
                exact ⟨hl, h⟩
              . rw [if_neg hr] at h
                right
                exact ⟨le_of_not_lt hr, h⟩ 
          . constructor <;> intro h
            apply Part.ext'
            . rfl
            . simp
              cases' h with r h
              have h' : (Nat.unpair (Nat.pair n r)).fst = (Nat.unpair m).fst := by rw [h]
              rw [Nat.unpair_pair] at h'
              simp at h'
              exact h'.symm
            simp at h
            use (Nat.unpair m).snd
            rw [← h, Nat.pair_unpair]            

    | right => sorry
    | pair f g _ _ => sorry
    | comp f g _ _=> sorry
    | prec f g _ _ => sorry
    | rfind f _ => sorry