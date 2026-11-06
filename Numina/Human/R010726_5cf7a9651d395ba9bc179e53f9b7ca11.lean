import Mathlib

/- What is the value of $x$ if $-\frac23(x-5) = \frac32(x+1)$? -/
theorem algebra_18666 (x : ℝ) : -2/3 * (x - 5) = 3/2 * (x + 1) ↔ x = 11/13 := by
  constructor
  intro h
  -- First we get rid of the fractions by multiplying both sides by $6$
  field_simp at h
  -- So $-4(x-5) = 9(x+1)$.
  ring_nf at h
  -- Solve for $x$
  apply congrArg (fun a ↦ a + x * 4) at h
  ring_nf at h
  symm at h
  rw [add_comm] at h
  apply eq_sub_of_add_eq at h
  apply congrArg (fun a ↦ a / 13) at h
  ring_nf at h
  exact h
  intro h
  rw [h]
  ring_nf
