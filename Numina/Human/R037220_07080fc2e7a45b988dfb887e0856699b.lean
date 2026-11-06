import Mathlib

/- An infinite geometric series has common ratio $1/8$ and sum 60.  What is the first term of the series? -/
theorem algebra_16750 {a : ℝ} (h : ∑' n : ℕ, a * (1 / 8) ^ n = 60) :
    a = 105 / 2 := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one] at h <;> norm_num at h <;> linarith