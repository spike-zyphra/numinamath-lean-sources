import Mathlib

/- The expression $\left(\frac{1}{23} \right)^{1000}$ is closest to what integer? -/
theorem algebra_21652 : round ((1 / 23 : ℝ)^1000) = 0 := by 
  norm_num [round_eq_zero_iff]