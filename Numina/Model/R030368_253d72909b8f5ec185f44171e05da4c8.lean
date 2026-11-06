import Mathlib

theorem algebra_181632 {d v1 v2 : ℝ} (hd : d > 0) (h1 : v1 > 0) (h2 : v2 > 0)
    (h3 : v2 * 0.5 = d - v1 * 0.5) (h4 : d = (v2 * 0.5 + 2) + (0.5 * v1 + v1 * 2 / v2)) :
    d = 24 ∧ v1 = 40 ∧ v2 = 8 := by
  have eq1 : d = (v1 + v2) / 2 := by
    ring_nf at h3 ⊢
    linarith
  rw [eq1] at h4
  have h5 : v2 > 0 := h2
  field_simp at h4
  <;> nlinarith [mul_pos h1 h2, mul_pos h1 (show (0 : ℝ) < 1 by linarith), mul_pos h2 (show (0 : ℝ) < 1 by linarith), mul_pos h1 h2]