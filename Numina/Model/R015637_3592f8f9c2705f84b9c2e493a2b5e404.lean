import Mathlib

theorem algebra_276
    (x y z : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z)
    (h : x + y + z = 1)
    (t : ℝ)
    (ht : t = 2 * x * y + y * z + 2 * z * x) :
    t ≤ 4 / 7 := by

  have h1 : z = 1 - x - y := by
    linarith

  rw [ht]
  rw [h1]

  nlinarith [sq_nonneg (x - 3 / 7), sq_nonneg (y - 2 / 7), sq_nonneg ((1 - x - y) - 2 / 7), 
          mul_nonneg hx hy, 
          mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith)
          ]