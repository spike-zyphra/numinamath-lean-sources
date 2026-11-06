import Mathlib

theorem algebra_1789 : ∑' n : ℕ, (9 / (10 ^ (n + 1)) : ℝ) = 1 := by
  have h : ∀ n : ℕ, (9 / (10 ^ (n + 1)) : ℝ) = 9 / 10 * (1 / 10) ^ n := by
    intro n
    field_simp
    <;> ring_nf <;> omega
  rw [tsum_congr h]
  rw [tsum_mul_left]
  rw [tsum_geometric_of_lt_one]
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num