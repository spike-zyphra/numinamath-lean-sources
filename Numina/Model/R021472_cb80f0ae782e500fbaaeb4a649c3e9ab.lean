import Mathlib

theorem algebra_183162 (x : ℝ) :
    8^x * (3 * x + 1) = 4 ↔ x = 1 / 3 := by
  constructor
  · -- First direction: If 8^x * (3 * x + 1) = 4 then x = 1/3
    intro h_eq
    have h1 : (8 : ℝ) ^ x = (2 : ℝ) ^ (3 * x) := by 
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h_eq2 : (2 : ℝ) ^ (3 * x) * (3 * x + 1) = (4 : ℝ) := by
      rw [h1] at h_eq
      linarith
    have h4 : 3 * x + 1 > 0 := by
      by_contra h
      push_neg at h
      have h5 : (2 : ℝ) ^ (3 * x) > 0 := by positivity
      have h6 : (2 : ℝ) ^ (3 * x) * (3 * x + 1) ≤ (0 : ℝ) := by 
        have h7 : (3 * x + 1) ≤ (0 : ℝ) := by nlinarith
        nlinarith [h5, h7]
      nlinarith [h_eq2, h6]
    have h7 : (2 : ℝ) ^ (3 * x) * (3 * x + 1) = (4 : ℝ) := h_eq2
    have h8 : (3 * x) + (Real.logb (2 : ℝ) (3 * x + 1)) = (2 : ℝ) := by
      have h9 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x) * (3 * x + 1)) = Real.logb (2 : ℝ) (4) := by
        rw [h7]
      have h10 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x) * (3 * x + 1)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x)) + Real.logb (2 : ℝ) (3 * x + 1) := by 
        rw [Real.logb_mul (by positivity) (by nlinarith)]
      have h11 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x)) = (3 * x) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h12 : Real.logb (2 : ℝ) (4 : ℝ) = (2 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h13 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 * x) * (3 * x + 1)) = (2 : ℝ) := by
        linarith [h9, h12]
      linarith [h10, h11, h13]
    have h5 : x = (1 / 3 : ℝ) := by
      have h8 : (3 * x : ℝ) + Real.logb (2 : ℝ) (3 * x + 1) = (2 : ℝ) := h8 
      by_cases h : x < (1 / 3 : ℝ)
      · -- Assume x < 1/3
        have h10 : 3 * x + 1 < (2 : ℝ) := by linarith
        have h11 : Real.logb (2 : ℝ) (3 * x + 1) < (1 : ℝ) := by
          have h9 : Real.logb (2 : ℝ) (3 * x + 1) < Real.logb (2 : ℝ) (2 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals nlinarith
          have h10 : Real.logb (2 : ℝ) (2 : ℝ) = (1 : ℝ) := by 
            norm_num
          nlinarith
        have h12 : (3 * x : ℝ) + Real.logb (2 : ℝ) (3 * x + 1) < (2 : ℝ) := by
          nlinarith
        linarith
      · -- Assume x = 1/3 or x > 1/3
        by_cases h' : x > (1 / 3 : ℝ)
        · -- Assume x > 1/3
          have h10 : 3 * x + 1 > (2 : ℝ) := by linarith
          have h11 : Real.logb (2 : ℝ) (3 * x + 1) > (1 : ℝ) := by
            have h9 : Real.logb (2 : ℝ) (3 * x + 1) > Real.logb (2 : ℝ) (2 : ℝ) := by
              apply Real.logb_lt_logb
              all_goals nlinarith
            have h10 : Real.logb (2 : ℝ) (2 : ℝ) = (1 : ℝ) := by 
              norm_num
            nlinarith
          have h12 : (3 * x : ℝ) + Real.logb (2 : ℝ) (3 * x + 1) > (2 : ℝ) := by
            nlinarith
          linarith
        · -- Case x = 1/3
          linarith
    linarith
  · -- Second direction: If x = 1/3, then 8^x * (3 * x + 1) = 4
    intro h_eq
    rw [h_eq]
    have h1 : (8 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h2 : (8 : ℝ) ^ (1 / 3 : ℝ) * (3 * (1 / 3 : ℝ) + 1) = (4 : ℝ) := by 
      rw [h1]
      norm_num
    linarith [h2]