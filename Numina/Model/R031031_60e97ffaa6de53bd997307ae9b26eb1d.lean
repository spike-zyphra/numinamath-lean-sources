import Mathlib

theorem algebra_21411 {x y : ℝ} (h₁ : (x + y) / 2 = 7) (h₂ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by

  have h3 : x + y = 14 := by
    linarith

  have h4 : x * y ≥ 0 := by
    by_contra h
    push_neg at h
    have h5 : Real.sqrt (x * y) = 0 := by 
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
    rw [h5] at h₂
    have h6 : Real.sqrt 19 = 0 := by
      linarith
    have h7 : Real.sqrt 19 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    linarith

  have h5 : x * y = 19 := by
    have h6 : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by
      rw [h₂]
    have h7 : (Real.sqrt (x * y)) ^ 2 = x * y := by
      exact Real.sq_sqrt (show 0 ≤ x * y by linarith)
    have h8 : (Real.sqrt 19) ^ 2 = 19 := by
      exact Real.sq_sqrt (show 0 ≤ 19 by norm_num)
    nlinarith

  have h8 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    nlinarith

  rw [h8, h3, h5]
  all_goals norm_num