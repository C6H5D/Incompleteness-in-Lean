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
def ψ_left  : BoundedArithmeticFormula 2 := ∃' (((&1 <' &2) ⊓ (((&2 ⬝' &2) +' &1) =' &0)) ⊔ ((&2 ≤' &1) ⊓ (((&1 ⬝' &1) +' &1 +' &2) =' &0)))
def ψ_right : BoundedArithmeticFormula 2 := ∃' (((&2 <' &1) ⊓ (((&1 ⬝' &1) +' &2) =' &0)) ⊔ ((&1 ≤' &2) ⊓ (((&2 ⬝' &2) +' &2 +' &1) =' &0)))

-- This requires some work

def ψ_pair (ψ_f ψ_g : BoundedArithmeticFormula 2) : BoundedArithmeticFormula 2 := ∃' ∃' ((liftAt 2 1 ψ_f) ⊓ (liftAt 2 2 ψ_g))

-- What we want to say is this:
-- ψ_pair (n,m) <-> ∃k ∃l, (f(n,k) ∧ g(n,l) ∧ (k < l ∧ l * l + l = m ∨ l ≤ k ∧ k * k + k + l = m))

-- But we need to tell the existence quantifier what to bind - or equivalently shuffle the free variables of f
-- I think what we need is liftAt

#check liftAt 3 20 ψ_succ

theorem a0 : (∃' (liftAt 1 0 ψ_succ)).Realize default ![10, 20] := by
   rw [ψ_succ,x0,x1]
   simp
   use 21
   simp
   rw [realize_liftAt]
   simp
   linarith

theorem a1 : (∃' (liftAt 1 1 ψ_succ)).Realize default ![10, 20] := by
   rw [ψ_succ,x0,x1]
   simp
   use 11
   simp
   rw [realize_liftAt]
   simp
   linarith

   -- Missing rules to simplify lift


-- @[simp] theorem Part.get_pure 

-- @[simp] lemma mylem : _ = _ := rfl

lemma pair_lemma : ∀ a b ab: ℕ, a < b ∧ b * b + a = ab ∨ b ≤ a ∧ a * a + a + b = ab ↔ (Nat.pair a b) = ab := by
    unfold Nat.pair
    intro a b ab
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
    · intro h
      have c := Nat.lt_or_ge a b
      cases' c with c0 c1
      · left
        rw [if_pos c0] at h
        exact ⟨c0, h⟩
      · right
        have ll : ¬a<b := Nat.not_lt.mpr c1
        rw [if_neg ll] at h
        exact ⟨c1, h⟩

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

        . intro ab a
          rw [ψ_left]
          simp
          constructor
          · intro h
            cases' h with b pairing
            rw [pair_lemma a b ab] at pairing
            rw [← pairing]
            rw [Nat.unpair_pair a b]
          · intro h
            let b := (Nat.unpair ab).snd
            use b
            rw [pair_lemma a b ab]
            simp
            rw [← h]
            exact Nat.pair_unpair ab

    | right =>
        use ψ_right
        constructor
        · sorry
        · intro ab b
          rw [ψ_right]
          simp
          constructor
          · intro h
            cases' h with a pairing
            rw [pair_lemma a b ab] at pairing
            rw [← pairing]
            rw [Nat.unpair_pair a b]
          · intro h
            let a := (Nat.unpair ab).fst
            use a
            rw [pair_lemma a b ab]
            simp
            rw [← h]
            exact Nat.pair_unpair ab

    | pair f g f_has_sigma1 g_has_sigma1 =>
        cases' f_has_sigma1 with f_form f_sigma1_realize
        cases' f_sigma1_realize with f_sigma1 f_realize
        cases' g_has_sigma1 with g_form g_sigma1_realize
        cases' g_sigma1_realize with g_sigma1 g_realize
        let ψ := ψ_pair f_form g_form
        use ψ
        constructor
        · sorry
        · sorry

    | comp f g _ _=> sorry
    | prec f g _ _ => sorry
    | rfind f _ => sorry