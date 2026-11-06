import Mathlib

open Real

theorem algebra_209025 {a b : ℝ}
    (ha : a = sqrt (sqrt 3 - sqrt 2) * (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)))
    (hb : b = sqrt (sqrt 3 + sqrt 2) * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1))) : a + b = 0 := by
  have h1 : 0 < sqrt 3 := by positivity
  have h2 : 0 < sqrt 2 := by positivity
  have h3 : sqrt 3 > sqrt 2 := by
    apply Real.sqrt_lt_sqrt
    all_goals norm_num
  have h4 : sqrt 3 ≥ sqrt 2 := by linarith
  have h5 : sqrt 3 - sqrt 2 ≥ 0 := by linarith
  have h6 : sqrt 3 ≥ 1 := by
    have h7 : Real.sqrt 3 ≥ Real.sqrt 1 := by
      apply Real.sqrt_le_sqrt
      norm_num
    have h8 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
    linarith [h7, h8]
  have h39 : 0 ≤ (Real.sqrt 3 - 1 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h10 : sqrt (sqrt 3 - 1) ≥ 0 := Real.sqrt_nonneg _
  have h11 : sqrt (sqrt 3 + 1) ≥ 0 := Real.sqrt_nonneg _
  have h8 : (a + b) ^ 2 = 0 := by
    have ha2 : a ^ 2 = 2 := by
      rw [ha]
      have h9 : sqrt (sqrt 3 - sqrt 2) ^ 2 = sqrt 3 - sqrt 2 := by
        rw [Real.sq_sqrt]
        have h12 : sqrt 3 ≥ sqrt 2 := by
          apply Real.sqrt_le_sqrt
          linarith
        have h13 : sqrt 3 - sqrt 2 ≥ 0 := by linarith
        linarith
      have h10 : (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)) ^ 2 = 2 * Real.sqrt 3 + 2 * Real.sqrt 2 := by
        have h11 : (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)) ^ 2 =
            (sqrt (sqrt 3 - 1)) ^ 2 + (sqrt (sqrt 3 + 1)) ^ 2 + 2 * (sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1)) := by ring
        rw [h11]
        have h12 : (sqrt (sqrt 3 - 1)) ^ 2 = sqrt 3 - 1 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 3 - 1), Real.sqrt_nonneg (sqrt 3 + 1)]
        have h14 : (sqrt (sqrt 3 + 1)) ^ 2 = sqrt 3 + 1 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 3 + 1)]
        have h13 : sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1) = Real.sqrt 2 := by
          have h14 : sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1) = sqrt ((sqrt 3 - 1) * (sqrt 3 + 1)) := by
            have h15 : (sqrt 3 - 1) ≥ 0 := by
              have h7 : sqrt 3 ≥ Real.sqrt 1 := by
                apply Real.sqrt_le_sqrt
                norm_num
              have h8 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
              linarith [h7, h8]
            have h16 : (sqrt 3 + 1) ≥ 0 := by
              have h7 : sqrt 3 ≥ 0 := by positivity
              linarith
            have h17 : sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1) = sqrt ((sqrt 3 - 1) * (sqrt 3 + 1)) := by
              rw [← Real.sqrt_mul (by nlinarith)]
            linarith
          rw [h14]
          have h18 : (sqrt 3 - 1) * (sqrt 3 + 1) = (2 : ℝ) := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          rw [h18]
          all_goals linarith
        nlinarith [h12, h13, h14]
      calc
        (sqrt (sqrt 3 - sqrt 2) * (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1))) ^ 2
          = sqrt (sqrt 3 - sqrt 2) ^ 2 * (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)) ^ 2 := by ring
        _ = (sqrt 3 - sqrt 2) * (2 * Real.sqrt 3 + 2 * Real.sqrt 2) := by rw [h9, h10]
        _ = 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), sq_nonneg (sqrt 3 ^ 2 - 3), sq_nonneg (sqrt 2 ^ 2 - 2)]
    have hb2 : b ^ 2 = 2 := by
      rw [hb]
      have h9 : sqrt (sqrt 3 + sqrt 2) ^ 2 = sqrt 3 + sqrt 2 := by
        rw [Real.sq_sqrt]
        have h10 : sqrt 3 + sqrt 2 ≥ 0 := by positivity
        linarith
      have h11 : (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1)) ^ 2 = 2 * Real.sqrt 3 - 2 * Real.sqrt 2 := by
        have h12 : (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1)) ^ 2 =
            (sqrt (sqrt 3 - 1)) ^ 2 + (sqrt (sqrt 3 + 1)) ^ 2 - 2 * (sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1)) := by ring
        rw [h12]
        have h13 : (sqrt (sqrt 3 - 1)) ^ 2 = sqrt 3 - 1 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 3 - 1), Real.sqrt_nonneg (sqrt 3 + 1)]
        have h14 : (sqrt (sqrt 3 + 1)) ^ 2 = sqrt 3 + 1 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 3 + 1)]
        have h15 : sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1) = Real.sqrt 2 := by
          have h14 : sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1) = sqrt ((sqrt 3 - 1) * (sqrt 3 + 1)) := by
            have h15 : (sqrt 3 - 1) ≥ 0 := by
              have h7 : sqrt 3 ≥ Real.sqrt 1 := by
                apply Real.sqrt_le_sqrt
                norm_num
              have h8 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
              linarith [h7, h8]
            have h16 : (sqrt 3 + 1) ≥ 0 := by
              have h7 : sqrt 3 ≥ 0 := by positivity
              linarith
            have h17 : sqrt (sqrt 3 - 1) * sqrt (sqrt 3 + 1) = sqrt ((sqrt 3 - 1) * (sqrt 3 + 1)) := by
              rw [← Real.sqrt_mul (by nlinarith)]
            linarith
          rw [h14]
          have h18 : (sqrt 3 - 1) * (sqrt 3 + 1) = (2 : ℝ) := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          rw [h18]
          all_goals linarith
        nlinarith [h13, h14, h15]
      calc
        (sqrt (sqrt 3 + sqrt 2) * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1))) ^ 2
          = sqrt (sqrt 3 + sqrt 2) ^ 2 * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1)) ^ 2 := by ring
        _ = (sqrt 3 + sqrt 2) * (2 * Real.sqrt 3 - 2 * Real.sqrt 2) := by rw [h9, h11]
        _ = 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), sq_nonneg (sqrt 3 ^ 2 - 3), sq_nonneg (sqrt 2 ^ 2 - 2)]
    have hab : a * b = -2 := by
      rw [ha, hb]
      have h9 : sqrt (sqrt 3 - sqrt 2) * sqrt (sqrt 3 + sqrt 2) = 1 := by
        have h10 : sqrt (sqrt 3 - sqrt 2) * sqrt (sqrt 3 + sqrt 2) = sqrt ((sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 2)) := by
          have h11 : (sqrt 3 - sqrt 2) ≥ 0 := by
            have h13 : sqrt 3 ≥ sqrt 2 := by
              apply Real.sqrt_le_sqrt
              all_goals linarith
            nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h12 : (sqrt 3 + sqrt 2) ≥ 0 := by positivity
          have h13 : sqrt (sqrt 3 - sqrt 2) * sqrt (sqrt 3 + sqrt 2) = sqrt ((sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 2)) := by
            rw [← Real.sqrt_mul (by nlinarith)]
          linarith
        rw [h10]
        have h11 : (sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 2) = 1 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h11]
        simp
      have h10 : (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)) * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1)) = -2 := by
        have h11 : (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)) * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1)) = (sqrt (sqrt 3 - 1)) ^ 2 - (sqrt (sqrt 3 + 1)) ^ 2 := by ring
        rw [h11]
        have h12 : (sqrt (sqrt 3 - 1)) ^ 2 = sqrt 3 - 1 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 3 - 1), Real.sqrt_nonneg (sqrt 3 + 1)]
        have h13 : (sqrt (sqrt 3 + 1)) ^ 2 = sqrt 3 + 1 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (sqrt 3 + 1)]
        nlinarith [h12, h13]
      calc
        (sqrt (sqrt 3 - sqrt 2) * (sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1))) * (sqrt (sqrt 3 + sqrt 2) * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1)))
            = (sqrt (sqrt 3 - sqrt 2) * sqrt (sqrt 3 + sqrt 2)) * ((sqrt (sqrt 3 - 1) + sqrt (sqrt 3 + 1)) * (sqrt (sqrt 3 - 1) - sqrt (sqrt 3 + 1))) := by ring
        _ = (1) * (-2) := by rw [h9, h10]
        _ = -2 := by norm_num
    calc
      (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
      _ = 2 + 2 * (-2) + 2 := by rw [ha2, hb2, hab]
      _ = (0 : ℝ) := by norm_num
  have h9 : (a + b) ^ 2 = 0 := h8
  have h10 : a + b = 0 := by
    nlinarith
  exact h10