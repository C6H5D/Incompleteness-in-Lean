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
 
instance true_arithmetic : Arithmetic.L_arithmetic.Structure ℕ := by
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
  BoundedFormula L_arithmetic Empty n

@[reducible]
def ArithmeticFormula :=
  Formula L_arithmetic Empty

example: ArithmeticFormula = BoundedArithmeticFormula 0 := rfl

@[reducible]
def BoundedArithmeticTerm (n : ℕ) :=
  Term L_arithmetic (Empty ⊕ Fin n)

@[reducible]
def ArithmeticTerm := BoundedArithmeticTerm 0

-- Operation Simplifications
def ArithmeticTerm.ofNat {l : ℕ} (n : ℕ) : BoundedArithmeticTerm l := by 
  induction' n with _ IH
  . exact Constants.term Arithmetic.zero
  . exact Functions.apply₁ Arithmetic.succ IH

instance : Coe ℕ ArithmeticTerm where
  coe := ArithmeticTerm.ofNat

attribute [coe] ArithmeticTerm.ofNat

prefix:max " succ' "  => (fun t => Functions.apply₁ Arithmetic.succ t)

infixl:90 " +' " => (fun t u => Functions.apply₂ Arithmetic.plus t u)

infixl:100 " ⬝' " => (fun t u => Functions.apply₂ Arithmetic.times t u)

infixl:100 " *' " => (fun t u => Functions.apply₂ Arithmetic.times t u)

infix:88 " ≤' " => (fun t u => Relations.boundedFormula₂ Arithmetic.le t u)

infix:88 " ≠' " => (fun t u => ∼ (t =' u))

infix:88 " <' " => (fun t u => (t ≤' u) ⊓ (t ≠' u))

infix:88 " ≥' " => (fun t u => (u ≤' t))

infix:88 " >' " => (fun t u => (u <' t))

----------- Bounded quantifier: use macro for bq; check Delta_0 by asking for a proof

open Std.ExtendedBinder
open Lean

syntax "∃' " binderIdent " <' " term ", " term : term

macro_rules
  | `(∃' $_:ident <' $y:term, $p) =>
    `(∃' ((&(Fin.last _) <' $y:term) ⊓ ($p)))

syntax "∃' " binderIdent " ≤' " term ", " term : term

macro_rules
  | `(∃' $_:ident ≤' $y:term, $p) =>
    `(∃' ((&(Fin.last _) ≤' $y:term) ⊓ ($p)))

syntax "∀' " binderIdent " <' " term ", " term : term

macro_rules
  | `(∀' $_:ident <' $y:term, $p) =>
    `(∀' ((&(Fin.last _) <' $y:term) ⟹ ($p)))

syntax "∀' " binderIdent " ≤' " term ", " term : term

macro_rules
  | `(∀' $_:ident ≤' $y:term, $p) =>
    `(∀' ((&(Fin.last _) ≤' $y:term) ⟹ ($p)))


def test : BoundedArithmeticFormula 2 := (&0 =' ArithmeticTerm.ofNat 11) ⊓ (&1 =' ArithmeticTerm.ofNat 17)
def eleven : BoundedArithmeticTerm 2 := &1
def test1 := ∃' test ⊓ (&0 ≠' &0)
def test2 := ∃' x <' eleven, test
def test3 := ∃' x ≤' eleven, test
def test4 := ∀' x ≤' eleven, test
def test5 := ∀' x <' eleven, test

#print test1

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
--   use ⊓ 

-- instance : Sup (L.BoundedFormula α n) :=
-- ⟨fun f g => f.not.imp g⟩
  -- use ⊔ 
