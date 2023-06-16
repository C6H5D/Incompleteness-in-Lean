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

#check Part.get

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
          have meaningFormula : ψ₀.Realize default ![m, n] ↔ 0 = n := by
            rfl
          rw [meaningFormula]
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
          have meaningFormula : ψ_succ.Realize default ![m, n] ↔ Nat.succ m = n := by
            rfl
          rw [meaningFormula]
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
          constructor
          . intro hrealize
            apply Part.ext'
            rfl
            . simp
              suffices : ∃ r, Nat.pair n r = m 
              . cases' this with r r_right
                rw [← r_right, Nat.unpair_pair]
              . simp [Nat.pair]
                suffices : ∃ r, (n < r ∧ r * r + n = m) ∨ (¬n < r ∧ n * n + n + r = m)
                . cases' this with r h
                  use r
                  cases' (em (n < r)) with hl hr
                  . rw [if_pos hl]
                    tauto
                  . rw [if_neg hr]
                    tauto
                . change (∃' _).Realize _ _ at hrealize
                  -- simp at hrealize
                  rw [BoundedFormula.realize_ex] at hrealize
                  cases' hrealize with r hrealize
                  use r
                  simp only [realize_sup, realize_inf, Arithmetic.realize_lt, Arithmetic.realize_ne, realize_bdEqual,
                    Arithmetic.realize_plus, Arithmetic.realize_times, Arithmetic.realize_le] at hrealize  
                  simp only [Pi.default_def, Function.comp_apply, Term.realize_var, Sum.elim_inr, ne_eq] at hrealize 
                  simp at hrealize

                  simp [lt_iff_le_and_ne.symm] at hrealize
                  rwa [not_lt]
                  
          . intro hfunc
            simp [BoundedFormula.Realize]
            intro hcontra
            specialize hcontra (Nat.unpair m).snd
            sorry


            

    | right => sorry
    | pair f g _ _ => sorry
    | comp f g _ _=> sorry
    | prec f g _ _ => sorry
    | rfind f _ => sorry
    


#check BoundedFormula
-- #check φ.Realize

def m : ℕ := 8
def n : ℕ := 9

def p : Prop :=  BoundedFormula.Realize ψ₀ default (fun x => by 
        induction x.val
        exact m
        exact n)
#check p
#check Part ℕ 
-- #check pure 0 p