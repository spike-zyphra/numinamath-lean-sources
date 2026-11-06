import Mathlib

theorem algebra_244045 (v1 v2 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0)
    (h3 : 10 / v1 = 10 / v2 + 3) (h4 : 2.5 / v2 = 2.5 / v1 + 2) :
    v2 / v1 = 2.5 := by
  field_simp [show v1 ≠ 0 by linarith, show v2 ≠ 0 by linarith] at h3 h4 ⊢
  ring_nf at h3 h4 ⊢
  nlinarith [mul_pos h1 h2, sq_pos_of_pos h1, sq_pos_of_pos h2, 
          sq_nonneg (v1 - v2), sq_nonneg (v1 - 2 * v2), sq_nonneg (2 * v1 - v2)
]