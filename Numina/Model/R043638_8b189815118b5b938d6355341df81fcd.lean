import Mathlib

theorem algebra_220514 (x : ℝ) :
    3 * 4^x + (3 * x - 10) * 2^x + 3 - x = 0 ↔ x = Real.logb 2 (1 / 3) ∨ x = 1 := by
  constructor
  · -- Forward implication: if equation holds, then x is one of the solutions
    intro h
    have h1 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x) := by
      calc
        (4 : ℝ) ^ x = (2 ^ (2 : ℝ) ) ^ x := by norm_num
        _ = 2 ^ (2 * x : ℝ) := by rw [← Real.rpow_mul]; ring_nf; all_goals norm_num
    have h2 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by
      calc
        (2 : ℝ) ^ (2 * x) = (2 ^ (x : ℝ) ) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring_nf; all_goals norm_num
        _ = ((2 : ℝ) ^ x) ^ 2 := by simp
    have h3 : (4 : ℝ) ^ x = ((2 : ℝ) ^ x) ^ 2 := by
      rw [h1, h2]
    rw [h3] at h
    have h4 : 3 * ((2 : ℝ) ^ x) ^ 2 + (3 * x - 10) * ((2 : ℝ) ^ x) + 3 - x = 0 := by
      linarith [h]
    have h5 : 3 * ((2 : ℝ) ^ x) ^ 2 + (3 * x - 10) * ((2 : ℝ) ^ x) + 3 - x = ( (2 : ℝ) ^ x - (1 / 3) ) * ( (2 : ℝ) ^ x + x - 3 ) := by
      nlinarith [sq_nonneg ( (2 : ℝ) ^ x - 1 ), sq_nonneg ( (2 : ℝ) ^ x - 2 ), sq_nonneg (x - 1), Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (2 * x), Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) x ]
    rw [h5] at h4
    cases' (mul_eq_zero.1 h4) with h6 h7
    · -- Case h6 : (2 : ℝ) ^ x - (1 / 3) = 0
      have h8 : (2 : ℝ) ^ x = 1 / 3 := by linarith
      have h9 : x = Real.logb 2 (1 / 3) := by
        rw [← h8]
        field_simp
      left
      exact h9
    · -- Case h7 : (2 : ℝ) ^ x + x - 3 = 0
      have h8 : (2 : ℝ) ^ x = 3 - x := by linarith
      have h10 : x = 1 := by
        by_cases h11 : x < 1
        · -- Assume x < 1
          have h12 : (2 : ℝ) ^ x < (2 : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
          have h13 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
          rw [h13] at h12
          have h14 : (2 : ℝ) ^ x < 2 := by linarith
          have h15 : (3 - x : ℝ) > 2 := by linarith
          nlinarith [h8, h14, h15, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x]
        · -- Assume x ≥ 1
          by_cases h12 : x > 1
          · -- Assume x > 1
            have h13 : (2 : ℝ) ^ x > (2 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt
              all_goals linarith
            have h14 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
            rw [h14] at h13
            have h15 : (2 : ℝ) ^ x > 2 := by linarith
            have h16 : (3 - x : ℝ) < 2 := by linarith
            nlinarith [h8, h15, h16, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x]
          · -- Assume x = 1
            have h17 : x = 1 := by linarith
            exact h17
      right
      exact h10
  · -- Backward implication: if x is one of the solutions, then equation holds
    rintro (h | h)
    · -- x = Real.logb 2 (1 / 3)
      rw [h]
      have h1 : (2 : ℝ) ^ (Real.logb 2 (1 / 3) : ℝ) = (1 / 3 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals norm_num
      have h3 : (4 : ℝ) ^ (Real.logb 2 (1 / 3) : ℝ) = ((2 : ℝ) ^ (Real.logb 2 (1 / 3) : ℝ) ) ^ 2 := by
        calc
          (4 : ℝ) ^ (Real.logb 2 (1 / 3) : ℝ) = (2 ^ (2 : ℝ) ) ^ (Real.logb 2 (1 / 3) : ℝ) := by norm_num
          _ = 2 ^ (2 * (Real.logb 2 (1 / 3) : ℝ) ) := by rw [← Real.rpow_mul]; ring_nf; all_goals norm_num
          _ = (2 ^ (Real.logb 2 (1 / 3) : ℝ) ) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring_nf; all_goals norm_num
      rw [h3, h1]
      nlinarith [h1, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (Real.logb 2 (1 / 3) : ℝ) ]
    · -- x = 1
      rw [h]
      norm_num