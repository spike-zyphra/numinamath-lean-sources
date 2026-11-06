import Mathlib

/- What is $\sqrt{53}$ in simplest radical form? -/
theorem algebra_21016 (a b : ℕ) (apos : a > 0) (bpos : b > 0) (hb : Squarefree b) (h : √53 = a * √b) : a = 1 ∧ b = 53 := by
  -- First, we square both sides of the equation.
  apply_fun (fun x => x ^ 2) at h
  -- Simplify h, and we get a^2 * b = 53.
  ring_nf at h
  simp at h
  norm_cast at h
  -- We have a * a ∣ 53.
  have k : a * a ∣ 53 := ⟨b, by rw [h]; ring⟩
  -- We have 53 is squarefree.
  have l : Squarefree 53 := by native_decide
  -- By the definition of squarefree, a is a unit.
  specialize l _ k
  -- 1 is the only unit in ℕ.
  have ha : a = 1 := Nat.isUnit_iff.1 l
  -- Substitute a = 1
  subst ha
  simp at h
  exact ⟨rfl, h.symm⟩