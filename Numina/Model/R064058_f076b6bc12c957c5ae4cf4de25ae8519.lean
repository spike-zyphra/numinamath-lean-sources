import Mathlib

theorem algebra_143615 (v : ℝ) (h : v > 0) (h' : 10 / v = 10 / (v + 5) + 10 / (v - 5)) :
    10 / v = 10 / (v + 5) + 10 / (v - 5) + 4 := by
  have h2 : v + 5 ≠ 0 := by
    linarith [h]
  have h3 : v - 5 ≠ 0 := by 
    by_contra h4
    have h5 : v = 5 := by linarith
    rw [h5] at h'
    norm_num at h'
  field_simp [show v ≠ 0 by linarith, show v + 5 ≠ 0 by assumption, show v - 5 ≠ 0 by assumption] at h' ⊢
  nlinarith [sq_nonneg v, sq_nonneg (v - 5), sq_nonneg (v + 5)]