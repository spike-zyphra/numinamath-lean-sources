import Mathlib

theorem algebra_21667 : (∑' n : ℕ, 0.03 * 0.1 ^ n : ℝ) / ∑' n : ℕ, 0.03 * 0.01 ^ n = 1 + 1 / 10 := by

  have h1 : ∑' n : ℕ, (0.03 * (0.1 : ℝ) ^ n) = (1 / 30 : ℝ) := by 
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  
  have h2 : ∑' n : ℕ, (0.03 * (0.01 : ℝ) ^ n) = (1 / 33 : ℝ) := by 
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  
  rw [h1, h2]
  norm_num