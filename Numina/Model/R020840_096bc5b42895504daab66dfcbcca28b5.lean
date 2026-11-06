import Mathlib

theorem algebra_116016 (x : ℝ) :
    Real.sqrt (abs (x - 1)) + Real.sqrt (abs (x - 2015)) = Real.sqrt 2014 ↔
    x = 1 ∨ x = 2015 := by
  constructor
  · -- First, prove the forward direction
    intro h_eq
    have h1 : Real.sqrt (abs (x - 1)) ≥ 0 := Real.sqrt_nonneg (abs (x - 1))
    have h2 : Real.sqrt (abs (x - 2015)) ≥ 0 := Real.sqrt_nonneg (abs (x - 2015))
    have h3 : Real.sqrt 2014 ≥ 0 := Real.sqrt_nonneg 2014
    have h4 : (Real.sqrt (abs (x - 1)) + Real.sqrt (abs (x - 2015)) ) ^ 2 = (Real.sqrt 2014) ^ 2 := by
      rw [h_eq]
    have h5 : (Real.sqrt (abs (x - 1)) + Real.sqrt (abs (x - 2015)) ) ^ 2 = (Real.sqrt (abs (x - 1)) ) ^ 2 + (Real.sqrt (abs (x - 2015)) ) ^ 2 + 2 * (Real.sqrt (abs (x - 1)) * Real.sqrt (abs (x - 2015)) ) := by ring
    have h6 : (Real.sqrt 2014) ^ 2 = (2014 : ℝ) := Real.sq_sqrt (by norm_num)
    have h7 : (Real.sqrt (abs (x - 1)) ) ^ 2 = abs (x - 1) := Real.sq_sqrt (abs_nonneg (x - 1))
    have h8 : (Real.sqrt (abs (x - 2015)) ) ^ 2 = abs (x - 2015) := Real.sq_sqrt (abs_nonneg (x - 2015))
    rw [h5, h6, h7, h8] at h4
    by_cases h10 : x ≥ 2015
    · -- Case x ≥ 2015
      have h11 : abs (x - 1) = x - 1 := by
        rw [abs_of_nonneg]
        linarith
      have h12 : abs (x - 2015) = x - 2015 := by
        rw [abs_of_nonneg]
        linarith
      rw [h11, h12] at h4
      have h13 : Real.sqrt (x - 1) * Real.sqrt (x - 2015) = 0 := by
        nlinarith [sq_nonneg (Real.sqrt (x - 1) - Real.sqrt (x - 2015)), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2015 by nlinarith), sq_nonneg (x - 2015), sq_nonneg (x - 1), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2015), sq_nonneg (Real.sqrt (x - 1) - (Real.sqrt (x - 2015)) ), mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (x - 2015))]
      cases' (mul_eq_zero.mp h13) with h14 h15
      · -- Real.sqrt (x - 1) = 0
        have h16 : x - 1 = 0 := by
          calc
            x - 1 = (Real.sqrt (x - 1)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
            _ = (0 : ℝ) ^ 2 := by rw [h14]
            _ = (0 : ℝ) := by norm_num
        have : x = 1 := by linarith
        right
        linarith
      · -- Real.sqrt (x - 2015) = 0
        have h17 : x - 2015 = 0 := by
          calc
            x - 2015 = (Real.sqrt (x - 2015)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
            _ = (0 : ℝ) ^ 2 := by rw [h15]
            _ = (0 : ℝ) := by norm_num
        have : x = 2015 := by linarith
        right
        linarith
    by_cases h11 : x ≤ 1
    · -- Case x ≤ 1
      have h12 : abs (x - 1) = (1 - x : ℝ) := by
        rw [abs_of_nonpos]
        linarith
        all_goals linarith
      have h13 : abs (x - 2015) = (2015 - x : ℝ) := by
        rw [abs_of_nonpos]
        linarith
        all_goals linarith
      rw [h12, h13] at h4
      have : x = 1 := by
        nlinarith [Real.sqrt_nonneg (1 - x), Real.sqrt_nonneg (2015 - x), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2015 - x : ℝ) by nlinarith), sq_nonneg (x - 1), sq_nonneg (x - 2015), Real.sqrt_nonneg (2015 - x), Real.sqrt_nonneg (1 - x), sq_nonneg (Real.sqrt (1 - x) - Real.sqrt (2015 - x) ), mul_nonneg (Real.sqrt_nonneg (1 - x)) (Real.sqrt_nonneg (2015 - x))]
      left
      linarith
    · -- Case 1 < x < 2015
      have h12 : x > 1 := by linarith
      have h13 : x < 2015 := by linarith
      have h14 : abs (x - 1) = x - 1 := by
        rw [abs_of_pos]
        linarith
      have h15 : abs (x - 2015) = (2015 - x : ℝ) := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      rw [h14, h15] at h4
      have h16 : Real.sqrt (x - 1) * Real.sqrt (2015 - x) = 0 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (2015 - x), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2015 - x : ℝ) by nlinarith), sq_nonneg (Real.sqrt (x - 1) - Real.sqrt (2015 - x) ), Real.sqrt_nonneg (2015 - x), Real.sqrt_nonneg (x - 1), sq_nonneg (x - 2015), sq_nonneg (x - 1), Real.sqrt_nonneg (2014), Real.sq_sqrt (show (0 : ℝ) ≤ 2014 by norm_num)]
      cases' (mul_eq_zero.mp h16) with h17 h18
      · -- Case Real.sqrt (x - 1) = 0
        have h18 : x - 1 = 0 := by
          calc
            x - 1 = (Real.sqrt (x - 1)) ^ 2 := by rw [Real.sq_sqrt]; linarith
            _ = (0 : ℝ) ^ 2 := by rw [h17]
            _ = (0 : ℝ) := by norm_num
        linarith
      · -- Case Real.sqrt (2015 - x) = 0
        have h19 : 2015 - x = 0 := by
          calc
            2015 - x = (Real.sqrt (2015 - x)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
            _ = (0 : ℝ) ^ 2 := by rw [h18]
            _ = (0 : ℝ) := by norm_num
        nlinarith
  · -- Backward direction
    intro h
    rcases h with (r | r)
    · -- Case x = 1
      rw [r]
      have h1 : abs ((1 : ℝ) - 1) = (0 : ℝ) := by
        norm_num [abs_of_nonneg]
      have h2 : abs ((1 : ℝ) - 2015) = (2014 : ℝ) := by
        norm_num [abs_of_nonpos, abs_of_pos]
      rw [h1, h2]
      have h3 : Real.sqrt (0 : ℝ) = 0 := by
        simp [Real.sqrt_eq_zero]
      rw [h3]
      all_goals
        norm_num [Real.sqrt_eq_zero]
    · -- Case x = 2015
      rw [r]
      have h1 : abs ((2015 : ℝ) - 1) = (2014 : ℝ) := by
        norm_num [abs_of_pos]
      have h2 : abs ((2015 : ℝ) - 2015) = (0 : ℝ) := by
        norm_num [abs_of_nonneg]
      rw [h1, h2]
      have h3 : Real.sqrt (0 : ℝ) = 0 := by
        simp [Real.sqrt_eq_zero]
      rw [h3]
      all_goals
        norm_num [Real.sqrt_eq_zero]