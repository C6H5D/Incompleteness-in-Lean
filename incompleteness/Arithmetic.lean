import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

namespace FirstOrder
namespace Language
namespace Arithmetic

inductive Constants : Type
  | zero

inductive UnaryFunctions : Type
  | succ

inductive BinaryFunctions : Type
  | plus
  | times

inductive Relations : Type
  | le

-- export Arithmetic.Constants (zero)
-- export Arithmetic.BinaryFunctions (plus times)
-- export Arithmetic.UnaryFunctions (succ)
-- export Arithmetic.Relations (le)

def L_arithmetic : Language :=
  Language.mk₂ Arithmetic.Constants Arithmetic.UnaryFunctions Arithmetic.BinaryFunctions Empty Arithmetic.Relations

protected def zero : (Arithmetic.L_arithmetic.Constants) := Constants.zero

protected def succ : (Arithmetic.L_arithmetic.Functions 1) := UnaryFunctions.succ

protected def plus : (Arithmetic.L_arithmetic.Functions 2) := BinaryFunctions.plus

protected def times : (Arithmetic.L_arithmetic.Functions 2) := BinaryFunctions.times

protected def le : (Arithmetic.L_arithmetic.Relations 2) := Relations.le

def true_arithmetic : Arithmetic.L_arithmetic.Structure ℕ := by
  apply Language.Structure.mk₂
  <;> intro a
  <;> cases' a
  . exact 0
  . exact Nat.succ
  . exact Nat.add
  . exact Nat.mul
  . exact Nat.le

-- Type Notation Simplifications
@[reducible]
def BoundedArithmeticFormula (n : ℕ) :=
  BoundedFormula L_arithmetic ℕ n

@[reducible]
def ArithmeticFormula :=
  Formula L_arithmetic ℕ

example: ArithmeticFormula = BoundedArithmeticFormula 0 := rfl

@[reducible]
def BoundedArithmeticTerm (n : ℕ) :=
  Term L_arithmetic (ℕ ⊕ Fin n)

@[reducible]
def ArithmeticTerm := BoundedArithmeticTerm 0

-- Operation Simplifications
def ArithmeticTerm.ofNat (n : ℕ) : ArithmeticTerm := by 
  induction' n with _ IH
  . exact Constants.term Arithmetic.zero
  . exact Functions.apply₁ Arithmetic.succ IH

instance : Coe ℕ ArithmeticTerm where
  coe := ArithmeticTerm.ofNat

-----------------Recall from ModelTheory.Syntax:-----------------

-- prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr
--   -- so &n is a term for n-th free variable in BoundedFormula

-- scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual
-- -- input \~- or \simeq

-- scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp
-- -- input \==>

-- scoped[FirstOrder] prefix:110 "∀'" => FirstOrder.Language.BoundedFormula.all

-- scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not
-- -- input \~, the ASCII character ~ has too low precedence

-- scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff
-- -- input \<=>

-- scoped[FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex
-- -- input \ex

-- instance : Top (L.BoundedFormula α n) :=
--   ⟨BoundedFormula.not ⊥⟩
  -- use by ⊥ of corresponding type

-- instance : Bot (L.BoundedFormula α n) :=
--   ⟨falsum⟩
  -- use by ⊤ of corresponding type

-- instance : Inf (L.BoundedFormula α n) :=
--   ⟨fun f g => (f.imp g.not).not⟩
  -- use ⊓ 

-- instance : Sup (L.BoundedFormula α n) :=
-- ⟨fun f g => f.not.imp g⟩
  -- use ⊔ 

