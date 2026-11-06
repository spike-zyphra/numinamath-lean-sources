import Mathlib

theorem algebra_114569 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / (1 + b) + b / (1 + a) = 1) : a^3 + b^3 = a + b := by
  have h1 : a / (1 + b) + b / (1 + a) = 1 := h
  have pos1 : 0 < 1 + a := by linarith
  have pos2 : 0 < 1 + b := by linarith
  field_simp [pos1, pos2] at h1
  ring_nf at h1
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_self_nonneg (a - 1),
    mul_self_nonneg (b - 1), mul_self_nonneg (a - b), mul_self_nonneg (a + b - 2)]
