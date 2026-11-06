import Mathlib

theorem algebra_170741 {x y : ℝ} (hxy : x ≠ y) (hsum : 1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) = 2 / (x * y + 1)) :
    1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 2 / (x * y + 1) = 2 := by 
  have h1 : (x * y + 1 : ℝ) ≠ 0 := by
    by_contra h
    have : 2 / (x * y + 1) = 0 := by
      rw [h]
      norm_num
    have h2 : 1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) = 0 := by
      linarith [hsum, this]
    have hx1_pos : 1 / (x ^ 2 + 1) > 0 := by
      apply div_pos
      norm_num
      nlinarith [sq_nonneg x]
    have hy1_pos : 1 / (y ^ 2 + 1) > 0 := by
      apply div_pos
      norm_num
      nlinarith [sq_nonneg y]
    nlinarith
  have h2 : (x ^ 2 + 1 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h3 : (y ^ 2 + 1 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg y]
  have eq1 : (x ^ 2 + y ^ 2 + 2) * (x * y + 1) = 2 * (x ^ 2 + 1) * (y ^ 2 + 1) := by
    have h4 : x ^ 2 + 1 ≠ 0 := h2
    have h5 : y ^ 2 + 1 ≠ 0 := h3
    have h6 : x * y + 1 ≠ 0 := h1
    field_simp [h4, h5, h6] at hsum ⊢
    nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by 
      intro h'
      apply hxy
      nlinarith
    ), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x + y)]
  have eq2 : x * y = 1 := by
    nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by 
      intro h'
      apply hxy
      nlinarith
    ), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x + y)]
  have h4 : x * y + 1 = 2 := by 
    have hxy1 : x * y = 1 := eq2
    linarith
  have h5 : 1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) = 2 / (x * y + 1) := by 
    linarith [hsum]
  calc
    1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 2 / (x * y + 1)
        = (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1)) + 2 / (x * y + 1) := by ring
    _ = (2 / (x * y + 1)) + 2 / (x * y + 1) := by 
      linarith [h5]
    _ = 2 := by 
      have h6 : 2 / (x * y + 1) = 1 := by
        rw [show x * y + 1 = 2 by linarith [h4]]
        norm_num
      rw [h6]
      all_goals norm_num [h4]