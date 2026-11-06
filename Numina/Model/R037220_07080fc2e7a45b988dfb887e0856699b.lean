import Mathlib

theorem algebra_16750 {a : ℝ} (h : ∑' n : ℕ, a * (1 / 8) ^ n = 60) :
    a = 105 / 2 := by
  have h2 : ∑' n : ℕ, a * (1 / 8 : ℝ) ^ n = a * (8 / 7 : ℝ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num
    all_goals ring_nf
  rw [h2] at h
  linarith