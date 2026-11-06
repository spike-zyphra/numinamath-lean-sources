import Mathlib

theorem algebra_184035 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : 2 * x + 3 * x * y ^ 2 + 2 * z = 36) :
    x ^ 2 * y ^ 2 * z ≤ 144 := by
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y ^ 2 - 2 / 3), sq_nonneg (z - 6),
    sq_nonneg (x * (y ^ 2 - 2 / 3)), sq_nonneg ((y ^ 2 - 2 / 3) * (z - 6)), sq_nonneg ((x - 6) * (z - 6)),
    mul_nonneg hx (show 0 ≤ y ^ 2 by positivity),
    mul_nonneg (mul_nonneg hx (show 0 ≤ y ^ 2 by positivity)) hz,
    sq_nonneg (2 * x - 2 * z), sq_nonneg (x * y * z - 12),
    sq_nonneg ((2 + 3 * y ^ 2) - 3), sq_nonneg ((2 + 3 * y ^ 2) - 2)
    ]