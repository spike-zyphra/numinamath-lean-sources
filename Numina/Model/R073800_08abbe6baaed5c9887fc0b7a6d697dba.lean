import Mathlib

theorem inequalities_4428 (x y : ℝ) (h : y ≥ y^3 + x^2 + abs x + 1) :
    x^2 + y^2 ≥ 1 := by
  by_cases h1 : x ≥ 0
  · -- If x ≥ 0, then |x| = x
    rw [abs_of_nonneg h1] at h
    nlinarith [sq_nonneg (x), sq_nonneg (x + 1 / 2), sq_nonneg (y + 1), sq_nonneg (y - 1)]
  · -- If x < 0, then |x| = -x
    rw [abs_of_neg (lt_of_not_ge h1)] at h
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg (y + 1), sq_nonneg (y - 1)]