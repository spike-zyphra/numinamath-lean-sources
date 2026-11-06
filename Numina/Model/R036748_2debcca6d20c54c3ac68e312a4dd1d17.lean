import Mathlib

open Real Set

/- If $x, y, z$ are all positive real numbers, and ${{x}^{2}}+{{y}^{2}}+{{z}^{2}}=1,$ then the minimum value of $S=\frac{{{(z+1)}^{2}}}{2xyz}$ is ___          ___. -/
theorem inequalities_11006 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    3 + 2 * sqrt 2 ≤ (z + 1)^2 / (2 * x * y * z) := by
  have h1 : 0 < 2 * x * y * z := by positivity

  have h2 : (z + 1)^2 / (2 * x * y * z) ≥ 3 + 2 * sqrt 2 := by
    have h1 : 0 < 2 * x * y * z := by positivity
    have h3 : (z + 1 : ℝ) ^ 2 ≥ (3 + 2 * sqrt 2) * (2 * x * y * z) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - z), sq_nonneg (x^2 + y^2 - 2 * z^2), sq_nonneg (z - (sqrt 2 - 1 : ℝ)), sq_nonneg (x * y - (sqrt 2 - 1)/2 * (z)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x^2 + y^2 - z^2), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    have h4 : (z + 1 : ℝ) ^ 2 / (2 * x * y * z) ≥ 3 + 2 * sqrt 2 := by
      have hx1 : 0 < 2 * x * y * z := by positivity 
      have h3' : (z + 1 : ℝ) ^ 2 ≥ (3 + 2 * sqrt 2) * (2 * x * y * z) := h3
      have hx3 : (2 * x * y * z) > 0 := by positivity 
      apply (le_div_iff₀ (by positivity)).mpr 
      linarith 
    linarith 
  linarith [h2]