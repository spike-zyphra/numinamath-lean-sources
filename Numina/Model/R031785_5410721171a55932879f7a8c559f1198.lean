import Mathlib

open Real

theorem algebra_231629 {x : ℝ} (hx : x ≠ 0) :
    (sqrt 2023 + sqrt 2022)^x - (sqrt 2023 - sqrt 2022)^x = sqrt 8088 ↔ x = 1 := by 
  constructor
  · -- Assume left equals right, prove x = 1
    intro h_eq
    have ha : sqrt 2023 + sqrt 2022 > 1 := by
      have h2 : sqrt 2022 > 1 := by
        have h3 : (2022 : ℝ) > (1 : ℝ) ^ 2 := by norm_num
        have h4 : sqrt 2022 > sqrt ((1 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
        rw [show sqrt ((1 : ℝ) ^ 2) = (1 : ℝ) by rw [Real.sqrt_sq (by norm_num)]] at h4
        linarith
      nlinarith [Real.sqrt_pos.mpr (show (2023 : ℝ) > 0 by norm_num : (2023 : ℝ) > 0)]
    have hb : sqrt 2023 - sqrt 2022 > 0 := by 
      apply sub_pos.mpr 
      apply (Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
      all_goals norm_num
    have h4 : (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) - (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) = sqrt 8088 := by
      have h5 : (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) = sqrt 2023 + sqrt 2022 := by simp
      have h6 : (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) = sqrt 2023 - sqrt 2022 := by simp
      rw [h5, h6]
      have h8 : sqrt 8088 = 2 * sqrt 2022 := by
        have h9 : (8088 : ℝ) = (4 : ℝ) * (2022 : ℝ) := by norm_num
        rw [h9]
        have h10 : sqrt (4 * (2022 : ℝ)) = sqrt (4 : ℝ) * sqrt (2022 : ℝ) := by 
          rw [Real.sqrt_mul (by norm_num)]
        rw [h10]
        have h11 : sqrt (4 : ℝ) = 2 := by
          rw [Real.sqrt_eq_cases]
          norm_num
        rw [h11]
        all_goals linarith
      rw [h8]
      nlinarith [Real.sqrt_nonneg 2023, Real.sqrt_nonneg 2022]
    have h5 : (sqrt 2023 + sqrt 2022) ^ x - (sqrt 2023 - sqrt 2022) ^ x = (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) - (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) := by linarith [h_eq, h4]
    by_cases h7 : x > (1 : ℝ)
    · -- Assume x > 1
      have h8 : (sqrt 2023 + sqrt 2022) ^ x - (sqrt 2023 - sqrt 2022) ^ x > (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) - (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) := by
        have h9 : (sqrt 2023 + sqrt 2022) ^ x > (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt 
          all_goals linarith [ha]
        have h10 : (sqrt 2023 - sqrt 2022) ^ x < (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt 
          all_goals 
            have h6 : (sqrt 2023 - sqrt 2022) < (1 : ℝ) := by nlinarith [Real.sqrt_nonneg 2023, Real.sqrt_nonneg 2022, Real.sq_sqrt (show (0 : ℝ) ≤ (2023 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2022 : ℝ) by norm_num)]
            all_goals nlinarith [hb, h6, h7]
        linarith 
      linarith [h5, h8, h4]
    · -- Case x ≤ 1 
      by_cases h8 : x < (1 : ℝ)
      · -- Assume x < 1 
        have h9 : (sqrt 2023 + sqrt 2022) ^ x < (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt 
          all_goals linarith [ha]
        have h10 : (sqrt 2023 - sqrt 2022) ^ x > (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt 
          all_goals 
            have h6 : (sqrt 2023 - sqrt 2022) < (1 : ℝ) := by nlinarith [Real.sqrt_nonneg 2023, Real.sqrt_nonneg 2022, Real.sq_sqrt (show (0 : ℝ) ≤ (2023 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2022 : ℝ) by norm_num)]
            all_goals nlinarith [hb, h6, h8]
        have h11 : (sqrt 2023 + sqrt 2022) ^ x - (sqrt 2023 - sqrt 2022) ^ x < (sqrt 2023 + sqrt 2022) ^ (1 : ℝ) - (sqrt 2023 - sqrt 2022) ^ (1 : ℝ) := by
          linarith 
        linarith [h5, h11, h4]
      · -- Case x = 1 
        have h9 : x = (1 : ℝ) := by linarith 
        linarith 
  · -- Assume x = 1, prove the equation
    intro h_eq
    rw [h_eq]
    have h2 : (sqrt 2023 + sqrt 2022 : ℝ) ^ (1 : ℝ) = sqrt 2023 + sqrt 2022 := by simp
    have h3 : (sqrt 2023 - sqrt 2022 : ℝ) ^ (1 : ℝ) = sqrt 2023 - sqrt 2022 := by simp
    rw [h2, h3]
    have h4 : sqrt 8088 = 2 * sqrt 2022 := by
      have h5 : (8088 : ℝ) = (4 : ℝ) * (2022 : ℝ) := by norm_num
      rw [h5]
      have h6 : sqrt (4 * (2022 : ℝ)) = sqrt (4 : ℝ) * sqrt (2022 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
      rw [h6]
      have h7 : sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h7]
      all_goals linarith
    rw [h4]
    nlinarith [Real.sqrt_nonneg 2023, Real.sqrt_nonneg 2022, Real.sq_sqrt (show (0 : ℝ) ≤ (2023 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2022 : ℝ) by norm_num)]