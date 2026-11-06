import Mathlib

theorem algebra_263704 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    0 < x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  constructor
  · -- Prove that the expression is positive
    nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
      mul_pos hx (show 0 < y * z by positivity), mul_pos hy (show 0 < x * z by positivity), 
      mul_pos hz (show 0 < x * y by positivity)
    ]
  · -- Show the expression is ≤7/27
    have h4 : z = 1 - x - y := by linarith
    rw [h4]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
      mul_pos hx hy, mul_pos hx (show 0 < 1 - x - y by nlinarith), 
      mul_pos hy (show 0 < 1 - x - y by nlinarith), 
      sq_nonneg (x + y - 2/3), sq_nonneg ((1 - x - y) - 2/3), 
      sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg ((1 - x - y) - 1/3)
    ]