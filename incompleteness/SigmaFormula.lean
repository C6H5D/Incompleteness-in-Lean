import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Incompleteness.Arithmetic

open FirstOrder
open FirstOrder.Language
open Arithmetic

namespace FirstOrder
namespace Language
namespace Arithmetic

inductive IsDelta0 : (BoundedArithmeticFormula n) → Prop
  | of_isQF {φ} (h : φ.IsQF) : IsDelta0 φ
  | bex_lt {φ t} (h : IsDelta0 φ): ((Sum.inr 0) ∉ (t.varFinset)) → IsDelta0 (∃' x <' t, φ)
  | bex_le {φ t} (h : IsDelta0 φ): ((Sum.inr 0) ∉ (t.varFinset)) → IsDelta0 (∃' x ≤' t, φ)
  | ball_lt {φ t} (h : IsDelta0 φ): ((Sum.inr 0) ∉ (t.varFinset)) → IsDelta0 (∀' x <' t, φ)
  | ball_le {φ t} (h : IsDelta0 φ): ((Sum.inr 0) ∉ (t.varFinset)) → IsDelta0 (∀' x ≤' t, φ)
-- Probably will want to add more closure properties later

inductive IsSigma1 : (BoundedArithmeticFormula n) → Prop
  | of_isDelta0 {φ} (h : IsDelta0 φ) : IsSigma1 φ
  | ex {φ} (h : IsSigma1 φ): IsSigma1 (∃' φ)
  | and {φ ψ} (h1 : IsSigma1 φ) (h2 : IsSigma1 ψ): IsSigma1 (φ ⊓ ψ)
  | or {φ ψ} (h1 : IsSigma1 φ) (h2 : IsSigma1 ψ): IsSigma1 (φ ⊔ ψ)