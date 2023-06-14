-----WARNING: This file is used for exercise purposes only. 
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Graph
import Incompleteness.Arithmetic

open FirstOrder
open FirstOrder.Language
open Arithmetic

namespace FirstOrder.Language

universe u v w u' v'

-- variable (L : FirstOrder.Language) (α : Type u') (n : ℕ)

-- This file is now useless; cf. IsQF, IsAtomic in ModelTheory.Syntax
inductive  QFFormula  {L : Language} {α : Type u'} {n : ℕ} : (L.BoundedFormula α n) →  Prop
  | falsum : QFFormula (falsum)
  | equal (t₁ t₂ : L.Term (Sum α (Fin n))) : QFFormula (t1 =' t2)
  | rel (R : L.Relations l) (ts : Fin l → L.Term (Sum α (Fin n))) : QFFormula (BoundedFormula.rel R ts)
  | imp {φ ψ} : QFFormula φ → QFFormula ψ → QFFormula (φ.imp ψ)

-- Test
example : Prop := by
  have L0 := FirstOrder.Language.empty
  have fs : (Formula L0 ℕ) := BoundedFormula.falsum
  have qf_fs := QFFormula (fs)
  
  have t0 : (Term L0 (ℕ ⊕ Fin 0)) := Language.Term.var (Sum.inl 0)
  have qf_eq : (QFFormula (t0 =' t0)) := by
    apply QFFormula.equal t0 t0

  have t1 : (Term L_arithmetic (ℕ ⊕ Fin 0)) := Language.Term.var (Sum.inl 1)
  have r0 : (L_arithmetic.Relations 2) := Arithmetic.le
  have f1 : (Formula L_arithmetic ℕ) := @BoundedFormula.rel L_arithmetic ℕ 0 2 r0 (fun _=> t1)
  have f1' : (Formula L_arithmetic ℕ) := Relations.boundedFormula₂ r0 t1 t1
  have : f1 = (@BoundedFormula.rel L_arithmetic ℕ 0 2 r0 (fun _=> t1)) := sorry
  have : f1 = f1' := sorry
  -- Also, how to simp typedefs?
  have qf_rel := QFFormula.rel r0 (fun _=> t1)

  have t2 : (Term L_arithmetic (ℕ ⊕ Fin 1)) := Language.Term.var (Sum.inl 1)
  have f2 : (BoundedFormula L_arithmetic ℕ 1) := @BoundedFormula.rel L_arithmetic ℕ 1 2 r0 (fun _=> t2)
  have f_ex := f2.ex
  have qf_imp := QFFormula.imp qf_rel qf_rel

  exact True



def v0 : ArithmeticTerm := Language.Term.var (Sum.inl 0)
def p0 : ArithmeticFormula := (v0 =' v0)
def p1 := ∼ p0
def p2 := p1 ⟹ p0
def p3 := p1 ⇔ p1
def p4 : ArithmeticFormula := ⊥
def p5 : ArithmeticFormula := ⊤
def p6 := p4 ⊓ p4
def p7 := p5 ⊔ p5

def x0 : BoundedArithmeticTerm 1 := &0
def q0 : BoundedArithmeticFormula 1 := (x0 =' x0)
def pq : ArithmeticFormula := ∃' q0

def zero_term : ArithmeticTerm := Constants.term Arithmetic.zero
def n : ArithmeticTerm := (0:ℕ) 

#check BoundedFormula.IsQF
example : (BoundedFormula.IsQF p0) := by
  apply BoundedFormula.IsQF.of_isAtomic
  apply BoundedFormula.IsAtomic.equal

