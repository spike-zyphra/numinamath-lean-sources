import Mathlib

theorem algebra_140414 (x : ℝ) : abs (x + 6) = -(x + 6) ↔ x ≤ -6 := by
  constructor
  · -- Forward direction: If abs (x + 6) = -(x + 6), then x ≤ -6
    intro h
    have h1 : x + 6 ≤ 0 := by
      apply abs_eq_neg_self.mp
      exact h
    linarith
  · -- Reverse direction: If x ≤ -6, then abs (x + 6) = -(x + 6)
    intro h
    have h1 : x + 6 ≤ 0 := by linarith
    rw [abs_of_nonpos h1]