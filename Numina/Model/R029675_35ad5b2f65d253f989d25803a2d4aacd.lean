import Mathlib

open Real

theorem algebra_107087 : 1 / (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) + 1 / (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) + 2 / (1 + sqrt 3) = -2 := by
  have h1 : (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
    positivity
  have h2 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
    have h3 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
    have h4 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 1 := by
      have h15 : (1 : ℝ) < (3 : ℝ) := by norm_num
      have h16 : (3 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_lt_rpow
        all_goals nlinarith
      have h17 : (1 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
        simp [Real.rpow_zero]
        all_goals linarith
      linarith
    have h5 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) < 0 := by linarith
    linarith
  have h6 : (1 + sqrt 3) ≠ 0 := by 
    positivity
  have eq1 : 1 / (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) + 1 / (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) = 2 / (1 - sqrt 3) := by
    have h3 : (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := h1
    have h4 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := h2
    have h5 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 3 := by
      have h6 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (3 : ℝ) ^ ((1 : ℝ) / 2) := by 
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals positivity
      rw [h6]
      rw [Real.sqrt_eq_rpow]
      all_goals norm_num
      all_goals positivity
    have h6 : (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) * (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) = 1 - sqrt 3 := by
      calc 
        (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) * (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) = 1 - ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
        _ = 1 - sqrt 3 := by rw [h5]
    field_simp [(show 1 + (3 : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 by exact h3), (show 1 - (3 : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 by exact h4), h6]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    all_goals positivity
  have eq2 : 2 / (1 - sqrt 3) + 2 / (1 + sqrt 3) = -2 := by
    have h18 : (1 - sqrt 3) ≠ 0 := by
      have h19 : sqrt 3 > 0 := by positivity
      have h20 : 1 - sqrt 3 ≠ 0 := by
        intro h
        have h21 : sqrt 3 = 1 := by linarith
        have h22 : sqrt 3 > 1 := by 
          have h23 : sqrt 1 < sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          have h24 : sqrt 1 = 1 := Real.sqrt_one
          linarith
        linarith 
      exact h20
    have h25 : (1 + sqrt 3) ≠ 0 := h6
    field_simp [(show 1 - sqrt 3 ≠ 0 by exact h18), (show 1 + sqrt 3 ≠ 0 by exact h25)]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
    all_goals positivity
  linarith [eq1, eq2]
  all_goals positivity