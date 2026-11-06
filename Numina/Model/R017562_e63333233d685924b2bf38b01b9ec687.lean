import Mathlib

theorem algebra_12071
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x + y = x * y)
    (h2 : x + y + z = x * y * z) :
    1 < z ∧ z ≤ 4 / 3 := by

  have h5 : z > 1 := by
    by_contra h5
    push_neg at h5
    have h6 : z ≤ 1 := by linarith
    have h4 : x * y + z = x * y * z := by linarith
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2)]

  have h6 : 1 < z := h5

  have h7 : z ≤ 4 / 3 := by
    have h4' : x * y + z = x * y * z := by linarith
    have h8 : x + y ≥ 4 := by
      have h9 : x + y = x * y := h1
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), mul_pos hx hy]
    have h9 : x * y > 0 := mul_pos hx hy
    have h10 : z ≤ 4 / 3 := by
      have h11 : x * y + z = x * y * z := by linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (z - 4 / 3), sq_nonneg ((x + y) - 4), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h8]
    linarith

  constructor
  · linarith
  · linarith