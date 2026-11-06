import Mathlib

open Real

theorem calculus_17161 :
    arccos ((2 * (-3) + 5 * 7) / (sqrt (2 ^ 2 + 5 ^ 2) * sqrt ((-3) ^ 2 + 7 ^ 2))) * 180 / π = 45 := by

  have h1 : (2 * (-3) + 5 * 7 : ℝ) / (sqrt (2 ^ 2 + 5 ^ 2) * sqrt ((-3) ^ 2 + 7 ^ 2)) = Real.sqrt 2 / 2 := by
    have h2 : sqrt ((2 : ℝ) ^ 2 + (5 : ℝ) ^ 2) = Real.sqrt 29 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]

    have h3 : sqrt ((-3 : ℝ) ^ 2 + (7 : ℝ) ^ 2) = Real.sqrt 58 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]

    have h4 : (2 * (-3) + 5 * 7 : ℝ) = 29 := by norm_num

    rw [h2, h3, h4]
    
    have h5 : Real.sqrt 29 * Real.sqrt 58 = Real.sqrt 2 * (29 : ℝ) := by
      calc
        Real.sqrt 29 * Real.sqrt 58 = Real.sqrt (29 * 58 : ℝ) := by
          rw [← Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt ((2 : ℝ) * (29 ^ 2 : ℝ)) := by norm_num
        _ = Real.sqrt (2 : ℝ) * Real.sqrt ((29 : ℝ) ^ 2 : ℝ) := by
          rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt (2 : ℝ) * (29 : ℝ) := by
          rw [Real.sqrt_sq (by norm_num)]

    field_simp [h5]
    <;> ring_nf <;> norm_num [Real.sq_sqrt]

  rw [h1]

  have h5 : arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
    have h6 : Real.sqrt 2 / 2 = Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      <;> ring_nf <;> norm_num
      <;> ring
    rw [h6]
    have h7 : arccos (Real.cos (Real.pi / 4)) = Real.pi / 4 := by
      apply arccos_cos
      all_goals linarith [Real.pi_pos]
    exact h7

  rw [h5]

  field_simp [Real.pi_pos]
  <;> linarith [Real.pi_gt_three]