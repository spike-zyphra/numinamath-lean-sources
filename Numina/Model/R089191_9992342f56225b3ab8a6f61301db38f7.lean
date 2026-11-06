import Mathlib

theorem algebra_4715 {a b c : ℝ} (ha : a ≠ 0) (h : (1 / 4) * (b - c) ^ 2 = (a - b) * (c - a)) :
    (b + c) / a = 2 := by
  have h1 : (b - c) ^ 2 = 4 * ((a - b) * (c - a)) := by 
    linarith [h]
  have h2 : (b - c) ^ 2 = b^2 - 2 * b * c + c^2 := by 
    ring
  have h3 : 4 * ((a - b) * (c - a)) = 4 * a * c - 4 * a^2 - 4 * b * c + 4 * a * b := by 
    ring
  rw [h2, h3] at h1
  have h4 : 4 * a^2 + b^2 + c^2 - 4 * a * b - 4 * a * c + 2 * b * c = 0 := by
    nlinarith [h1]
  have h5 : (b + c - 2 * a) ^ 2 = 0 := by
    nlinarith [h4]
  have h6 : b + c - 2 * a = 0 := by 
    rw [sq_eq_zero_iff] at h5
    exact h5
  have h7 : b + c = 2 * a := by linarith [h6]
  field_simp [ha]
  linarith [h7]