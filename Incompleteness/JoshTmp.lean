import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Computability.PartrecCode
import Incompleteness.Arithmetic

namespace FirstOrder
namespace Language
namespace Arithmetic

def x0 : BoundedArithmeticTerm 2 := &0
def x1 : BoundedArithmeticTerm 2 := &1
-- def q0 : BoundedArithmeticFormula 1 := (x0 =' x0)
-- def pq : ArithmeticFormula := ∃' q0
-- variable (φ : BoundedFormula L_arithmetic ℕ 2)
def φ : BoundedArithmeticFormula 2 := (x0 =' x1)
def ψ₀ : BoundedArithmeticFormula 2 := (x1 =' (ArithmeticTerm.ofNat 0))
def ψ_succ  : BoundedArithmeticFormula 2 := (x1 =' succ' (ArithmeticTerm.ofNat 0))

-- ℝ → (y : ℝ) → y ≠ 0 → ℝ

#check Part.get

-- @[simp] theorem Part.get_pure 

-- ![m, n]

theorem part_rec_implies_sigma_one_definable {f : ℕ →. ℕ} {hf : Nat.Partrec f} :
        ∃ φ : BoundedFormula L_arithmetic ℕ 2, φ.IsQF ∧ ∀ m n : ℕ, φ.Realize default ![m, n] ↔ (f m = pure n) := by 
    induction hf with
    | zero => 
        use ψ₀
        constructor
        . sorry
        . intro m n
          constructor
          . intro hrealize
            apply Part.ext'
            rfl
            . simp
              intro h
              change 0 = _
              sorry
          . intro hpure
            simp [BoundedFormula.Realize, Term.realize]
            exact Iff.mp PartENat.natCast_inj (id (Eq.symm hpure))

    | succ => 
        use ψ_succ
        constructor
        . sorry
        . intro m n
          constructor
          . intro hrealize
            apply Part.ext'
            simp
            intro h₁ h₂
            simp
            unfold BoundedFormula.Realize at hrealize
            dsimp at hrealize

            sorry
          sorry
    | left => sorry
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