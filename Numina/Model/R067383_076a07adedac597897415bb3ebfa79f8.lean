import Mathlib

open Real

theorem algebra_145570 {a : ℝ} (ha : |a| < 1) :
    ∑' n : ℕ, a ^ n = 1 / (1 - a) := by 
  rw [tsum_geometric_of_norm_lt_one]
  all_goals
    simpa using ha