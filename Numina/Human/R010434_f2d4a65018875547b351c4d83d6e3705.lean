import Mathlib

/- The relationship between $2.3^{2.3}$ and $2.3^{3.2}$ is $2.3^{2.3}$ $2.3^{3.2}$ (express the relationship using an inequality). -/
theorem algebra_9011 : (2.3 : ℝ)^(2.3 : ℝ) < (2.3 : ℝ)^(3.2 : ℝ) := by
  -- 2.3 > 1
  -- 2.3 < 3.2
  -- Therefore, 2.3^2.3 < 2.3^3.2
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
