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