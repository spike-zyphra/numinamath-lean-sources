import Mathlib

theorem algebra_281282 (x : ℝ) (hx : x > 0) (h : (100 * x + 50 * (14 * x) - 50 * (14 * x) - 200 * (14 * x)) / (14 * x) = 2) :
    x ≤ 250 := by
  have h1 : 14 * x ≠ 0 := by
    nlinarith
  field_simp [h1] at h
  nlinarith