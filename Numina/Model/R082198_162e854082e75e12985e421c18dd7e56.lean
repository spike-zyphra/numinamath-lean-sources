import Mathlib

theorem algebra_236659 (v : ℝ) (h : v > 0) (h1 : 30 / v = 100 - 30 / (v - 10)) (h2 : 20 / v = 100 - 20 / (v - 10) + 5 / 60) :
    v = 100 := by
  field_simp [(show v ≠ 0 by linarith),
            (show v - 10 ≠ 0 by
              by_contra h'
              have h10 : v = 10 := by linarith
              rw [h10] at h1
              norm_num at h1
            )] at h1 h2 ⊢
  nlinarith [sq_nonneg (v - 100), sq_nonneg (v - 10)]