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
def ψ_left : BoundedArithmeticFormula 2 := ∃' (((&1 <' &2) ⊓ (((&2 ⬝' &2) +' &1) =' &0)) ⊔ ((&2 ≤' &1) ⊓ (((&1 ⬝' &1) +' &1 +' &2) =' &0)))

-- @[simp] theorem Part.get_pure 

-- @[simp] lemma mylem : _ = _ := rfl

lemma pair_lemma : ∀ a n m: ℕ, n < a ∧ a * a + n = m ∨ a ≤ n ∧ n * n + n + a = m ↔ (Nat.pair n a) = m := by
    unfold Nat.pair
    intro a n m
    constructor
    · intro h
      cases' h with h1 h2
      · cases' h1 with l r
        rw [if_pos l]
        exact r
      · cases' h2 with l r
        have ll := Nat.not_lt.mpr l
        rw [if_neg ll]
        exact r

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
        use ψ_left
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
          rw [ψ_left]
          simp
          constructor
          · intro h
            cases' h with a pairing
            rw [pair_lemma a n m] at pairing
            rw [← pairing]
            rw [Nat.unpair_pair n a]
          · intro h
            let a := (Nat.unpair m).snd
            use a
            rw [pair_lemma a n m]
            simp
            rw [← h]
            exact Nat.pair_unpair m

    | right => sorry
    | pair f g _ _ => sorry
    | comp f g _ _=> sorry
    | prec f g _ _ => sorry
    | rfind f _ => sorry