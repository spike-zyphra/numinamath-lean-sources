import Mathlib

theorem algebra_307009 {a b c : ℝ} (h : a ≠ 0) (h1 : (1 / 4) * (b - c) ^ 2 = (a - b) * (c - a)) :
    (b + c) / a = 2 := by
  have eq1 : (b - c) ^ 2 = 4 * (a - b) * (c - a) := by
    linarith
  have h2 : (b + c - 2 * a) ^ 2 = 0 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 2 * a)]
  have h3 : b + c - 2 * a = 0 := by
    rw [sq_eq_zero_iff] at h2
    exact h2
  have h4 : b + c = 2 * a := by
    linarith
  have h5 : (b + c) / a = (2 * a) / a := by
    rw [h4]
  have h6 : (2 * a) / a = 2 := by
    field_simp [h]
  rw [h5, h6]