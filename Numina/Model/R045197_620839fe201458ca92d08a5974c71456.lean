import Mathlib

open Real

theorem algebra_104793 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    (x + y) * (x + z) ≥ 2 := by
  have h1 : (x + y) * (x + z) = x * (x + y + z) + y * z := by
    ring
  have h2 : x * (x + y + z) + y * z ≥ 2 := by
    have h4 : x * (x + y + z) * (y * z) = 1 := by
      have h5 : x * y * z * (x + y + z) = 1 := h
      have h6 : x * (x + y + z) * (y * z) = x * y * z * (x + y + z) := by
        ring
      rw [h6]
      linarith [h5]
    nlinarith [sq_nonneg (x * (x + y + z) - 1), sq_nonneg (y * z - 1),
      sq_nonneg (x * (x + y + z) * (y * z) - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]
  linarith [h1, h2]