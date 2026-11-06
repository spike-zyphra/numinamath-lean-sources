import Mathlib

open Real

theorem algebra_21345 : ∑' n : ℕ, ((3 * (3 ^ n)):ℝ) / (2 * (103 ^ (n + 1))) = 0.015 := by
  have h1 : ∀ n : ℕ, ((3 * (3 ^ n)) : ℝ) / (2 * (103 ^ (n + 1))) = (3 / (2 * 103)) * (3 / 103) ^ n := by
    intro n
    field_simp
    <;> ring_nf
  rw [tsum_congr h1]
  rw [tsum_mul_left, tsum_geometric_of_lt_one]
  all_goals norm_num