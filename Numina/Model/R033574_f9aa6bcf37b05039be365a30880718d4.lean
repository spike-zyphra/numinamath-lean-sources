import Mathlib

open Real

theorem calculus_23081 : sin (π / 10) ^ 3 + sin (π / 10) ^ 2 = 1 / 8 := by
  have h1 : sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
    have h2 : sin (3 * (π / 10)) = 3 * sin (π / 10) - 4 * sin (π / 10) ^ 3 := by
      rw [sin_three_mul]
    have h3 : cos (2 * (π / 10)) = 1 - 2 * sin (π / 10) ^ 2 := by
      have h3a : cos (2 * (π / 10)) = 1 - 2 * sin (π / 10) ^ 2 := by
        rw [cos_two_mul, sin_sq]
        all_goals ring
      linarith
    have h4 : sin (3 * (π / 10)) = cos (2 * (π / 10)) := by
      have h5 : 3 * (π / 10) = π / 2 - 2 * (π / 10) := by
        linarith [pi_pos]
      rw [h5]
      rw [sin_pi_div_two_sub]
    rw [h2, h3] at h4
    have h5 : 4 * sin (π / 10) ^ 3 - 2 * sin (π / 10) ^ 2 - 3 * sin (π / 10) + 1 = 0 := by
      nlinarith [h4, sq_nonneg (sin (π / 10) ^ 2 - 1), sq_nonneg (sin (π / 10) ^ 2), sq_nonneg (sin (π / 10) ) ]
    have h6 : (sin (π / 10) - 1) * (4 * sin (π / 10) ^ 2 + 2 * sin (π / 10) - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · 
      have h9 : sin (π / 10) = 1 := by linarith
      have h10 : sin (π / 10) < 1 := by
        have h11 : sin (π / 10) < sin (π / 2) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith [pi_pos]
        have h12 : sin (π / 2) = 1 := by
          rw [sin_pi_div_two]
        nlinarith [h12]
      linarith
    · 
      have h11 : 4 * sin (π / 10) ^ 2 + 2 * sin (π / 10) - 1 = 0 := by linarith
      have h12 : sin (π / 10) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals 
          linarith [pi_pos]
      have h13 : sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
        have h14 : 4 * sin (π / 10) ^ 2 + 2 * sin (π / 10) - 1 = 0 := h11
        have h15 : (sin (π / 10) - (Real.sqrt 5 - 1) / 4) * (sin (π / 10) - (-Real.sqrt 5 - 1) / 4) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
        cases' (mul_eq_zero.1 h15) with h16 h17
        · 
          linarith
        · 
          have h18 : sin (π / 10) = (-Real.sqrt 5 - 1) / 4 := by linarith
          have h19 : sin (π / 10) < 0 := by
            nlinarith [Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
          linarith
      linarith
  rw [h1]
  nlinarith [Real.sqrt_pos.mpr (show 0 < 5 by norm_num : (0 : ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 5 ^ 2 - 5) ]