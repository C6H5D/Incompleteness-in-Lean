import Mathlib.ModelTheory.Basic
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

#check Language.Structure.mk₂

def true_arithmetic : Arithmetic.L_arithmetic.Structure ℕ := by
  apply Language.Structure.mk₂
  <;> intro a
  <;> cases' a
  . exact 0
  . exact Nat.succ
  . exact Nat.add
  . exact Nat.mul
  . exact Nat.le