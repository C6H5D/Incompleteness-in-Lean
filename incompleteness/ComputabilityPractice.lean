import Mathlib.Computability.PartrecCode

theorem add' : Nat.Primrec (Nat.unpaired (· + ·)) := by
  exact Nat.Primrec.add

#check Nat.unpaired (· + ·)
theorem add_plus_one : Nat.Primrec (Nat.unpaired (· + ·) + 1) := by
  apply Nat.Primrec.succ.comp Nat.Primrec.add

#check Nat.casesOn

theorem predecessor' : @Nat.Primrec' 1 (fun v => v.head.pred) := by
  have tmp := Nat.Primrec'.prec (Nat.Primrec'.zero) (Nat.Primrec'.head)
  simp at tmp
  apply Nat.Primrec'.of_eq
  exact tmp
  intro i
  cases Vector.head i
  simp
  simp
  -- apply Nat.Primrec.prec Nat.Primrec.zero

theorem predecessor : Primrec (Nat.pred) := by
  have tmp := predecessor'
  rw [Nat.Primrec'.prim_iff₁] at tmp
  exact tmp

#check Vector ℕ 1
-- convert between vec of length 1 and ℕ 