import Mathlib

theorem number_theory_2744 : (1 / 8 : ℝ) = ∑' n : ℕ, 1 / 9 ^ (n + 1) := by
  have h : ∀ n : ℕ, (1 / 9 ^ (n + 1) : ℝ) = (1 / 9) * (1 / 9) ^ n := by
    intro n
    field_simp
    <;> ring_nf <;> norm_num
  rw [tsum_congr h]
  rw [tsum_mul_left]
  rw [tsum_geometric_of_lt_one]
  all_goals norm_num