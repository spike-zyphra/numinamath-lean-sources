import Mathlib

theorem algebra_292564 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    -1 / 8 ≤ (z - x) * (z - y) ∧ (z - x) * (z - y) ≤ 1 := by
  constructor
  · -- Prove -1/8 ≤ (z - x) * (z - y)
    nlinarith [sq_nonneg (z - 1 / 4), sq_nonneg (x - y), sq_nonneg (x - (1 - z)), sq_nonneg (y - (1 - z)), 
      mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz
    ]
  · -- Prove (z - x) * (z - y) ≤ 1
    nlinarith [sq_nonneg (z - 1), sq_nonneg (x - y), sq_nonneg (x - 0), sq_nonneg (y - 0), 
      mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz
    ]