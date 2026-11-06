import Mathlib

theorem algebra_176580 (t : ℝ) (ht : t > 0) (h : 4 * t - 0.75 * t^2 = 3.5 * t + 0.5 * t^2 + 10) :
    t = 5 ∧ ¬(4 * t - 0.75 * t^2 < 23) := by 
  have h1 : 1.25 * t ^ 2 - 0.5 * t + 10 = 0 := by
    ring_nf at h ⊢
    nlinarith
  have h2 : 1.25 * t ^ 2 - 0.5 * t + 10 > 0 := by
    nlinarith [sq_nonneg (t - 0.2 / 1.25), sq_nonneg (t - 5 / 2)]
  linarith