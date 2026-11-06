import Mathlib
theorem algebra_21857 {x : ℝ} (hx : x = ∑' n : ℕ, ((0.1 ^ n) : ℝ) * 6) :
    x * 0.60 = 4 := by
  have h1 : x = (20 : ℝ) / 3 := by
    rw [hx]
    have h2 : ∀ n : ℕ, ((0.1 : ℝ) ^ n) * 6 = 6 * (0.1 : ℝ) ^ n := by
      intro n
      ring
    rw [tsum_congr h2]
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one]
    all_goals norm_num
  rw [h1]
  norm_num