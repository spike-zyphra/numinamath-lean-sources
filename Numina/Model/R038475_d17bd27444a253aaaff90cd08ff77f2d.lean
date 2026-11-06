import Mathlib

open Real

theorem algebra_327681 : 3 * tan (10 * π / 180) + 4 * sqrt 3 * sin (10 * π / 180) = sqrt 3 := by
  have htan : tan (10 * π / 180) = sin (10 * π / 180) / cos (10 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  have h1 : 10 * π / 180 = (π / 18) := by
    linarith [Real.pi_pos]
  rw [h1]
  have h2 : cos (π / 18) ≠ 0 := by
    have h3 : 0 < π / 18 := by
      linarith [Real.pi_pos]
    have h4 : cos (π / 18) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith
    linarith
  have eq1 : 3 * (sin (π / 18) / cos (π / 18)) + 4 * sqrt 3 * sin (π / 18) =
          (3 * sin (π / 18) + 4 * sqrt 3 * sin (π / 18) * cos (π / 18)) / cos (π / 18) := by
    field_simp [h2]
    <;> nlinarith
  have eq2 : (3 * sin (π / 18) + 4 * sqrt 3 * sin (π / 18) * cos (π / 18)) / cos (π / 18) = sqrt 3 := by
    have eq3 : 3 * sin (π / 18) + 4 * sqrt 3 * sin (π / 18) * cos (π / 18) = sqrt 3 * cos (π / 18) := by
      have h3 : sin (3 * (π / 18)) = 1 / 2 := by
        have h4 : 3 * (π / 18) = π / 6 := by
          ring_nf
        rw [h4]
        have h5 : sin (π / 6) = 1 / 2 := by
          exact sin_pi_div_six
        linarith
      have h4 : sin (3 * (π / 18)) = 3 * sin (π / 18) - 4 * sin (π / 18) ^ 3 := by
        rw [sin_three_mul]
      have h5 : cos (3 * (π / 18)) = Real.sqrt 3 / 2 := by
        have h6 : 3 * (π / 18) = π / 6 := by
          ring_nf
        rw [h6]
        have h7 : cos (π / 6) = Real.sqrt 3 / 2 := by
          exact cos_pi_div_six
        linarith
      have h6 : cos (3 * (π / 18)) = 4 * cos (π / 18) ^ 3 - 3 * cos (π / 18) := by
        rw [cos_three_mul]
      have h7 : sin (π / 18) ^ 2 + cos (π / 18) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (π / 18)
      nlinarith [sq_nonneg (sin (π / 18) - 1 / 2), sq_nonneg (cos (π / 18) - Real.sqrt 3 / 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
          sq_nonneg (sin (π / 18) - Real.sqrt 3 / 2), 
          sq_nonneg (cos (π / 18) - 1 / 2)
        ]
    have h8 : (3 * sin (π / 18) + 4 * sqrt 3 * sin (π / 18) * cos (π / 18)) / cos (π / 18) = sqrt 3 := by
      rw [eq3]
      field_simp [h2]
    linarith
  linarith [eq1, eq2]