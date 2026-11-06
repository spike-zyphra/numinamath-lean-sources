import Mathlib

theorem algebra_199528 (v : ℝ) (h : v > 0) (h' : 11 / v = 10 / (v - 11) + 45 / (v - 11)) :
    v = 11 := by
  have h1 : v ≠ 0 := by linarith
  have h2 : v - 11 ≠ 0 := by
    by_contra h3
    have h3' : v = 11 := by linarith
    rw [h3'] at h'
    norm_num at h' ⊢ <;> nlinarith
  field_simp [h1, h2] at h'
  nlinarith