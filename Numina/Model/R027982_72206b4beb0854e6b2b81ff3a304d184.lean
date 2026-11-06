import Mathlib

open Real Set

theorem inequalities_305312 {x : ℝ} (hx : ∀ a > 0, x^2 < 1 + a) :
    x ≤ 1 ∧ x ≥ -1 := by
  have h1 : x ^ 2 ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : x ^ 2 - 1 > 0 := by nlinarith
    have h2' := hx (x ^ 2 - 1) (by nlinarith)
    nlinarith
  have h2 : x ≤ 1 := by
    nlinarith [sq_nonneg (x - 1), h1]
  have h3 : x ≥ -1 := by
    nlinarith [sq_nonneg (x + 1), h1]
  constructor
  · exact h2
  · exact h3