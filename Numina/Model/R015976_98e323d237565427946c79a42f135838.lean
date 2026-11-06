import Mathlib

open Real

theorem inequalities_297003 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (f : ℝ → ℝ → ℝ → ℝ)
    (hf : f = fun x y z => ((x^2 + y^2)^3 + z^6) / (2 * x^3 * y^3 + y^3 * z^3 + z^3 * x^3)) :
    f x y z ≥ 2 := by
  have h1 : f x y z = ((x^2 + y^2)^3 + z^6) / (2 * x^3 * y^3 + y^3 * z^3 + z^3 * x^3) := by
    rw [hf]
  rw [h1] at *
  have pos1 : 0 < (2 * x^3 * y^3 + y^3 * z^3 + z^3 * x^3 : ℝ) := by
    positivity
  have h6 : ((x^2 + y^2)^3 + z^6) ≥ 2 * (2 * x^3 * y^3 + y^3 * z^3 + z^3 * x^3) := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2), 
      sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
      sq_nonneg (x * y - y * z), sq_nonneg (x * y - z * x), sq_nonneg (y * z - z * x), 
      sq_nonneg (x * z - y * z), sq_nonneg (x * y - x * z), sq_nonneg (y * x - y * z), 
      sq_nonneg (z^3 - 2 * x^3 - 2 * y^3), 
      sq_nonneg (z^2 - x^2 - y^2), 
      sq_nonneg (z^3 - (x^3 + y^3)), 
      sq_nonneg (x^3 - y^3), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos (show 0 < x^3 by positivity) (show 0 < y^3 by positivity), 
      sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
      pow_two_nonneg (x - y), pow_two_nonneg (x - z), pow_two_nonneg (y - z), 
      mul_pos (show 0 < x ^ 2 by positivity) (show 0 < y ^ 2 by positivity)
    ]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith [h6]