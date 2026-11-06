import Mathlib

open Real

theorem inequalities_240552 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ x * y * z) :
    (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ sqrt 3 := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ sqrt 3 := by
    have pos1 : 0 < x * y * z := h1
    apply (le_div_iff₀ pos1).mpr
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        h, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
        sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        sq_nonneg (x * y * z - (x + y + z)), 
        mul_self_nonneg (x * y * z - (x + y + z)), 
        sq_nonneg (x^2 + y^2 + z^2 - 3 * (x*y*z)^2), 
        Real.sqrt_nonneg 3, 
        sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2)
        ]
  exact h2