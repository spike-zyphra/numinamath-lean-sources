import Mathlib

theorem algebra_13250 : 1 - (∑' n : ℕ, (9 : ℝ) * 0.1 ^ (n + 1)) = 0 := by 
  have h : ∑' n : ℕ, (9 : ℝ) * 0.1 ^ (n + 1) = 1 := by
    have h1 : ∀ n : ℕ, (9 : ℝ) * 0.1 ^ (n + 1) = (9 : ℝ) * 0.1 * (0.1) ^ n := by 
      intro n
      ring_nf
    rw [tsum_congr h1]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
    all_goals norm_num
  
  rw [h]
  all_goals norm_num
  all_goals norm_num