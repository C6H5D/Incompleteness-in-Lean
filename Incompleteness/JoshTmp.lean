import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Computability.PartrecCode
import Incompleteness.Arithmetic

namespace FirstOrder
namespace Language
namespace Arithmetic

def x0 : BoundedArithmeticTerm 1 := &0
def q0 : BoundedArithmeticFormula 1 := (x0 =' x0)
def pq : ArithmeticFormula := ∃' q0
variable (φ : BoundedFormula L_arithmetic ℕ 2)


theorem part_rec_implies_sigma_one_definable {f : ℕ →. ℕ} {hf : Nat.Partrec f} :
        ∃ φ : BoundedFormula L_arithmetic ℕ 2, φ.IsQF ∧ ∀ m n : ℕ, BoundedFormula.Realize φ m n ↔ (f m = n) := by
    induction hf with
    | zero => sorry
    | succ => sorry
    | left => sorry
    | right => sorry
    | pair f g _ _ _ _ => sorry
    | comp f g _ _ _ _ => sorry
    | prec f g _ _ _ _ => sorry
    | rfind f _ _ => sorry
    


#check BoundedFormula
#check φ.Realize

#check @BoundedFormula.Realize 