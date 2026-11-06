import Mathlib

theorem algebra_152266 (x : ℝ) :
    (x^2 - abs x - 2)^2 + Real.sqrt (abs (2 * x + 1) - 3) = 0 ↔ x = -2 := by
  constructor
  · -- Forward: if the equation holds, then x = -2
    intro h
    have h1 : (x^2 - abs x - 2)^2 ≥ 0 := by
      apply sq_nonneg
    have h2 : Real.sqrt (abs (2 * x + 1) - 3) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : (x^2 - abs x - 2)^2 = 0 := by
      nlinarith [h1, h2, h]
    have h4 : Real.sqrt (abs (2 * x + 1) - 3) = 0 := by
      nlinarith [h1, h2, h]
    have h5 : abs (2 * x + 1) - 3 = 0 := by
      by_cases h6' : abs (2 * x + 1) - 3 ≥ 0
      · -- Case where the value under sqrt is non-negative
        have h7 : (Real.sqrt (abs (2 * x + 1) - 3)) ^ 2 = abs (2 * x + 1) - 3 := by
          rw [Real.sq_sqrt]
          linarith
        have h8 : (Real.sqrt (abs (2 * x + 1) - 3)) ^ 2 = 0 := by
          rw [h4]
          norm_num
        have h9 : abs (2 * x + 1) - 3 = 0 := by
          nlinarith
        linarith
      · -- Case where the value under sqrt is negative
        have h6' : abs (2 * x + 1) - 3 < 0 := by linarith 
        have h7 : Real.sqrt (abs (2 * x + 1) - 3) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith 
          all_goals linarith 
        have h8 : (x^2 - abs x - 2)^2 = 0 := by
          nlinarith [h, h7] 
        have h9 : x^2 - abs x - 2 = 0 := by
          nlinarith 
        -- Now show this leads to a contradiction by checking cases for x
        cases' abs_cases x with hx hx
        · -- Case x ≥ 0, so |x| = x
          have h10 : x^2 - x - 2 = 0 := by
            rw [show abs x = x by linarith] at h9
            linarith 
          have h11 : (x - 2) * (x + 1) = 0 := by
            nlinarith 
          cases' (mul_eq_zero.mp h11) with h12 h13
          · -- x = 2 
            have h2' : x = 2 := by linarith 
            rw [h2'] at h6' 
            norm_num at h6' 
          · -- x = -1 
            have h1' : x = -1 := by nlinarith 
            linarith 
        · -- Case x < 0, so |x| = -x
          have h10 : x^2 + x - 2 = 0 := by
            rw [show abs x = -x by linarith] at h9
            linarith 
          have h11 : (x + 2) * (x - 1) = 0 := by
            nlinarith 
          cases' (mul_eq_zero.mp h11) with h12 h13
          · -- x = -2 
            have h2' : x = -2 := by linarith 
            rw [h2'] at h6' 
            norm_num at h6' 
          · -- x = 1 
            have h1' : x = 1 := by nlinarith 
            linarith 
    have h6 : abs (2 * x + 1) = 3 := by
      linarith [h5] 
    have h7 : x^2 - abs x - 2 = 0 := by
      nlinarith [h3] 
    cases' eq_or_eq_neg_of_abs_eq h6 with h8 h8
    · -- Case where 2x + 1 = 3, so x = 1
      have h8' : x = 1 := by
        linarith 
      rw [h8'] at h7 
      norm_num [abs_of_nonneg, abs_of_nonpos] at h7 
    · -- Case where -(2x + 1) = 3, so x = -2
      have h9 : x = -2 := by
        linarith 
      exact h9 
  · -- Backward: if x = -2, then the equation holds
    intro h
    rw [h]
    have h1 : abs ((-2 : ℝ) ) = 2 := by norm_num [abs_of_nonneg, abs_of_nonpos]
    have h2 : abs (2 * (-2 : ℝ) + 1) = 3 := by norm_num [abs_of_nonneg, abs_of_nonpos]
    have h3 : Real.sqrt (abs (2 * (-2 : ℝ) + 1) - 3) = 0 := by
      rw [h2]
      norm_num [Real.sqrt_eq_zero]
      all_goals linarith 
    rw [h1, h3]
    all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
  all_goals linarith