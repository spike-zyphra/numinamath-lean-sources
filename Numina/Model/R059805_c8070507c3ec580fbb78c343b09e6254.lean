import Mathlib

open Real

theorem algebra_209033 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    17 / 4 ≤ a * b + 1 / (a * b) := by
  have h1 : 0 < a * b := by
    apply mul_pos
    all_goals linarith
  have h2 : a * b ≤ (a + b)^2 / 4 := by
    have h3 : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
    nlinarith
  rw [h] at h2
  have h3 : a * b ≤ 1 / 4 := by
    nlinarith
  have h4 : 4 * (a * b)^2 - 17 * (a * b) + 4 ≥ 0 := by
    nlinarith [sq_nonneg (a * b - 1 / 4), sq_nonneg (a * b - 4), h3, h1]
  have h5 : a * b + 1 / (a * b) - 17 / 4 ≥ 0 := by
    have h6 : 0 < a * b := h1
    have h7 : 4 * (a * b)^2 - 17 * (a * b) + 4 ≥ 0 := h4
    have h8 : (a * b + 1 / (a * b) - 17 / 4) = (4 * (a * b)^2 - 17 * (a * b) + 4) / (4 * (a * b)) := by
      field_simp
      ring
    rw [h8]
    apply div_nonneg
    linarith
    positivity
  linarith