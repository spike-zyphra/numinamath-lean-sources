import Mathlib

/- Calculate the sum of the geometric series $1+\left(\frac{1}{3}\right)+\left(\frac{1}{3}\right)^2 + \left(\frac{1}{3}\right)^3 + \dots$. Express your answer as a common fraction. -/
theorem algebra_10504 : ∑' n : ℕ, (1 / 3 : ℝ) ^ n = 3 / 2 := by
  rw [tsum_geometric_of_lt_one]
  norm_num
  simp
  norm_num
