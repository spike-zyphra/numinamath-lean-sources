import Mathlib

open Real

theorem algebra_253941 : (sqrt 6 + sqrt 2) * (sqrt 3 - 2) * sqrt (sqrt 3 + 2) = -2 := by
  have h1 : sqrt 6 = sqrt 2 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h3 : (sqrt 6 + sqrt 2) = sqrt 2 * (sqrt 3 + 1) := by
    rw [h1]
    all_goals ring_nf
  have h4 : (sqrt 6 + sqrt 2) * (sqrt 3 - 2) = sqrt 2 * (1 - sqrt 3) := by
    rw [h3]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 3), sq_nonneg (sqrt 2), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  have h41 : (sqrt 2 * (1 - sqrt 3) ) * sqrt (sqrt 3 + 2) = -2 := by
    have h42 : sqrt (sqrt 3 + 2) ≥ 0 := by positivity
    have h5 : sqrt 3 ≥ 0 := by positivity
    have h6 : sqrt 2 ≥ 0 := by positivity
    have h11 : sqrt (sqrt 3 + 2) ^2 = sqrt 3 + 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h43 : (sqrt 2 * (1 - sqrt 3) * sqrt (sqrt 3 + 2)) ^2 = 4 := by
      calc
        (sqrt 2 * (1 - sqrt 3) * sqrt (sqrt 3 + 2)) ^2
          = (sqrt 2) ^2 * ((1 - sqrt 3) )^2 * (sqrt (sqrt 3 + 2)) ^2 := by ring
        _ = 2 * ((1 - sqrt 3) )^2 * (sqrt (sqrt 3 + 2)) ^2 := by
          have h7 : (sqrt 2) ^2 = 2 := Real.sq_sqrt (by norm_num)
          rw [h7]
        _ = 2 * ((1 - sqrt 3) )^2 * (sqrt 3 + 2) := by
          rw [h11]
        _ = 2 * ((1 - sqrt 3) ^2) * (sqrt 3 + 2) := by ring
        _ = 2 * ((1 - 2* sqrt 3 + (sqrt 3) ^2)) * (sqrt 3 + 2) := by
          ring_nf
        _ = 2 * (1 - 2 * sqrt 3 + 3) * (sqrt 3 + 2) := by
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        _ = 2 * (4 - 2 * sqrt 3) * (sqrt 3 + 2) := by ring_nf
        _ = 4 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h44 : sqrt 2 * (1 - sqrt 3) * sqrt (sqrt 3 + 2) ≤ 0 := by
      have h45 : sqrt (sqrt 3 + 2) ≥ 0 := by positivity
      have h46 : sqrt 2 ≥ 0 := by positivity
      have h47 : (1 - sqrt 3) ≤ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      nlinarith [show sqrt 2 * (1 - sqrt 3) ≤ 0 by nlinarith [h46, h47], h45, mul_nonneg (show sqrt 2 >= 0 by positivity) (show sqrt (sqrt 3 + 2) >= 0 by positivity)]
    have h48 : (sqrt 2 * (1 - sqrt 3) * sqrt (sqrt 3 + 2) ) ^2 = 4 := h43
    have h49 : sqrt 2 * (1 - sqrt 3) * sqrt (sqrt 3 + 2) = -2 := by
      nlinarith [h48, h44]
    nlinarith
  calc
    (sqrt 6 + sqrt 2) * (sqrt 3 - 2) * sqrt (sqrt 3 + 2)
      = ((sqrt 6 + sqrt 2) * (sqrt 3 - 2)) * sqrt (sqrt 3 + 2) := by ring
    _ = (sqrt 2 * (1 - sqrt 3)) * sqrt (sqrt 3 + 2) := by rw [h4]
    _ = -2 := by linarith [h41]