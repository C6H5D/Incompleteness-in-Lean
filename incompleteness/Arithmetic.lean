import Mathlib.ModelTheory.Basic
namespace FirstOrder
namespace Language

inductive Arithmetic.Constants : Type
  | zero

inductive Arithmetic.BinaryFunctions : Type
  | plus
  | times

inductive Arithmetic.UnaryFunctions : Type
  | succ

inductive Arithmetic.Relations : Type
  | le

-- export Arithmetic.Constants (zero)
-- export Arithmetic.BinaryFunctions (plus times)
-- export Arithmetic.UnaryFunctions (succ)
-- export Arithmetic.Relations (le)

protected def arithmetic : Language :=
  Language.mk₂ Arithmetic.Constants Arithmetic.UnaryFunctions Arithmetic.BinaryFunctions Empty Arithmetic.Relations

#check Language.Structure.mk₂

def true_arithmetic : Language.arithmetic.Structure ℕ := by
  apply Language.Structure.mk₂
  <;> intro a
  <;> cases' a
  . exact 0
  . exact Nat.succ
  . exact Nat.add
  . exact Nat.mul
  . exact Nat.le