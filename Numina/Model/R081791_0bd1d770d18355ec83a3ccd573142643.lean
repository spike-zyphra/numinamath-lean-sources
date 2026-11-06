import Mathlib

open Real

theorem inequalities_322998 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a > b) :
    a^3 + 12 / (b * (a - b)) ≥ 20 := by
  have h1 : 0 < a - b := by linarith
  have h2 : 0 < b * (a - b) := by
    positivity
  have h3 : a^3 * b * (a - b) + 12 - 20 * (b * (a - b)) ≥ 0 := by
    nlinarith [sq_nonneg (a^2 - 4), sq_nonneg (a - 2), sq_nonneg (b - 1),
      sq_nonneg (a - 2 * b), mul_pos ha hb, h1, sq_nonneg (a * b - 4), sq_nonneg (a - b - 1)]
  have h4 : a^3 + 12 / (b * (a - b)) - 20 ≥ 0 := by
    have h5 : 0 < b * (a - b) := by
      positivity
    have h6 : a^3 * b * (a - b) + 12 - 20 * (b * (a - b)) ≥ 0 := by 
      linarith [h3]
    have h7 : a^3 + 12 / (b * (a - b)) - 20 = (a^3 * b * (a - b) + 12 - 20 * (b * (a - b))) / (b * (a - b)) := by
      field_simp [h5]
      <;> ring
    rw [h7]
    apply div_nonneg
    linarith [h6]
    positivity
  linarith [h4]