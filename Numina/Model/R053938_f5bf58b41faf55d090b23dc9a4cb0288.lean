import Mathlib

theorem algebra_178500 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + b^2 / a = b + a^2 / b) : a = b := by
  have h1 : a + b^2 / a = b + a^2 / b := h
  field_simp [ha, hb] at h1
  have h2 : a^2 * b + b^3 = a * b^2 + a^3 := by linarith [h1]
  have h3 : a^2 * b - a * b^2 + b^3 - a^3 = 0 := by linarith [h2]
  have h4 : (a^2 + b^2) * (b - a) = 0 := by
    linarith [h3]
  have h5 : a^2 + b^2 ≠ 0 := by
    by_contra h6
    have h7 : a^2 ≥ 0 := by nlinarith
    have h8 : b^2 ≥ 0 := by nlinarith
    have h9 : a^2 = 0 := by linarith [h6, h7, h8]
    have h10 : a = 0 := pow_eq_zero h9
    contradiction
  cases (mul_eq_zero.mp h4) with
  | inl h6 =>
    exfalso
    exact h5 h6
  | inr h7 =>
    linarith