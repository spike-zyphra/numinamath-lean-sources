import Mathlib

theorem inequalities_7555 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x ^ 2 + y ^ 3 + z ^ 4 ≥ x ^ 3 + y ^ 4 + z ^ 5) : (x ^ 3 + y ^ 3 + z ^ 3 ≤ 3 ∧ x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) := by
  constructor
  · -- Prove x^3 + y^3 + z^3 ≤ 3
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      sq_nonneg (x^2 - x), sq_nonneg (y^2 - y), sq_nonneg (z^2 - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      mul_pos (show 0 < x ^ 2 by nlinarith) (show 0 < y ^ 2 by nlinarith)
    ]
  · -- Prove x^2 + y^2 + z^2 ≤ 3
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      sq_nonneg (x^2 - x), sq_nonneg (y^2 - y), sq_nonneg (z^2 - z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      mul_pos (show 0 < x ^ 2 by nlinarith) (show 0 < y ^ 2 by nlinarith)
    ]