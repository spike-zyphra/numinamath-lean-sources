import Mathlib

open Real

theorem algebra_4639 : ∑' n : ℕ, ((2 : ℝ) ^ n + (3 : ℝ) ^ n) / (6 : ℝ) ^ n = 7 / 2 := by
  have h1 : ∑' n : ℕ, ((2 : ℝ) ^ n + (3 : ℝ) ^ n) / (6 : ℝ) ^ n =
    ∑' n : ℕ, ((2 / (6 : ℝ)) ^ n + (3 / (6 : ℝ)) ^ n) := by
    congr 
    funext n
    field_simp
    <;> ring
  rw [h1]
  rw [tsum_add]
  · -- First sum
    have h2 : ∑' n : ℕ, ((2 / (6 : ℝ)) ^ n) = (3 / 2) := by
      rw [show (2 / (6 : ℝ)) = (1 / 3 : ℝ) by norm_num]
      rw [tsum_geometric_of_norm_lt_one]
      all_goals norm_num
    have h3 : ∑' n : ℕ, ((3 / (6 : ℝ)) ^ n) = (2 : ℝ) := by
      rw [show (3 / (6 : ℝ)) = (1 / 2 : ℝ) by norm_num]
      rw [tsum_geometric_of_norm_lt_one]
      all_goals norm_num
    rw [h2, h3]
    all_goals norm_num
  all_goals -- Show the summability of the two series
    try { 
      simp_all [tsum_geometric_of_norm_lt_one, summable_geometric_of_norm_lt_one]
      <;> norm_num
    }