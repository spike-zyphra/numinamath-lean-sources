import Mathlib

theorem algebra_194219 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 7 / a = 7 / b + 3) (h2 : 7 / b = 7 / a + 1.5) :
    1 / a = 14 ∧ 1 / b = 14 := by
  have h3 : 7 * b = 7 * a + 3 * (a * b) := by
    field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith)] at h1 ⊢
    nlinarith
  have h4 : 7 * a = 7 * b + 1.5 * (a * b) := by
      field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith)] at h2 ⊢
      nlinarith
  constructor
  · -- Show that 1 / a = 14.
    field_simp [(show a ≠ 0 by linarith)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  · -- Show that 1 / b = 14.
    field_simp [(show b ≠ 0 by linarith)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]