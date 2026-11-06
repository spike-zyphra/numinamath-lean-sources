import Mathlib

theorem algebra_14348 : (∑' n : ℕ, 0.72 * 0.01 ^ n) / ∑' n : ℕ, 0.27 * 0.01 ^ n = (8 / 3 : ℝ) := by
  have h1 : ∑' n : ℕ, 0.72 * 0.01 ^ n = (0.72 / (1 - 0.01) : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num

  have h2 : ∑' n : ℕ, 0.27 * 0.01 ^ n = (0.27 / (1 - 0.01) : ℝ) := by 
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  
  rw [h1, h2]
  norm_num