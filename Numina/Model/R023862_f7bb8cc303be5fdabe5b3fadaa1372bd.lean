import Mathlib

theorem number_theory_11927 : 28 / 99 = ∑' n : ℕ, 28 * (0.01 : ℝ) ^ (n + 1) := by 
  have h : ∑' n : ℕ, 28 * (0.01 : ℝ) ^ (n + 1) = (28 / 99 : ℝ) := by 
    have h1 : ∀ n : ℕ, (28 * (0.01 : ℝ) ^ (n + 1)) = (28 * (0.01 : ℝ) ) * (0.01 : ℝ) ^ n := by
      intro n 
      ring_nf
      <;> norm_num 
    rw [tsum_congr h1]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h] 
  all_goals norm_num