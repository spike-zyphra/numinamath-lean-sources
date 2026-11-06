import Mathlib

open Real

/- Calculate the sum of the geometric series $1+\left(\frac{1}{5}\right)+\left(\frac{1}{5}\right)^2 + \left(\frac{1}{5}\right)^3 + \dots$. Express your answer as a common fraction. -/
theorem algebra_15301 : ∑' n : ℕ, (1 / 5 : ℚ)^n = 5 / 4 := by
  rw [tsum_geometric_of_norm_lt_one]
  . norm_num
  . simp
    have : ‖(5 : ℚ)‖ = 5 := by
      rw [← sub_zero 5, ← dist_eq_norm, ← Rat.dist_cast]
      simp
    norm_num [this]
