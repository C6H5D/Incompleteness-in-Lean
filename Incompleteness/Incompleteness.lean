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

-- ℝ → (y : ℝ) → y ≠ 0 → ℝ

#check Part.get

-- @[simp] theorem Part.get_pure 

theorem part_rec_implies_sigma_one_definable {f : ℕ →. ℕ} {hf : Nat.Partrec f} :
        ∃ φ : BoundedFormula L_arithmetic Empty 2, (IsSigma1 φ) ∧ ∀ m n : ℕ, φ.Realize default ![m, n] ↔ (f m = pure n) := by 
    induction hf with
    | zero => 
        use ψ₀
        constructor
        . apply IsSigma1.of_isDelta0 
          apply IsDelta0.of_isQF
          apply BoundedFormula.IsQF.of_isAtomic
          apply BoundedFormula.IsAtomic.equal
        . intro m n
          constructor
          . intro hrealize
            apply Part.ext'
            rfl
            . simp
              intro h
              change 0 = _
              exact hrealize

          . intro hfunc
            simp [BoundedFormula.Realize, Term.realize]

            rw [← PartENat.natCast_inj]
            exact hfunc

    | succ => 
        use ψ_succ
        constructor
        . apply IsSigma1.of_isDelta0 
          apply IsDelta0.of_isQF
          apply BoundedFormula.IsQF.of_isAtomic
          apply BoundedFormula.IsAtomic.equal
        . intro m n
          constructor
          . intro hrealize
            apply Part.ext'
            rfl
            . simp
              exact hrealize

          . intro hfunc
            simp [BoundedFormula.Realize, Term.realize]
            rw [← PartENat.natCast_inj]
            exact hfunc
    | left => 
        use ψ_left
        constructor
        . apply IsSigma1.ex
          apply IsSigma1.of_isDelta0
          apply IsDelta0.or <;> apply IsDelta0.and

          apply IsDelta0.and
          case left.left.h.h.h1.h1.h2 =>
            change IsDelta0 (∼(y2 =' y0))
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
                suffices : ∃ r, (n < r → r * r + n = m) ∧ (¬n < r → n * n + n + r = m)
                . sorry
                . sorry


          . intro hfunc
            apply realize_ex.mpr
            simp
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

-- Package Σ₁-soundness and effective axiomatizability