import Mathlib

theorem algebra_196221 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 75) (h2 : y^2 + y * z + z^2 = 49) (h3 : z^2 + x * z + x^2 = 124) :
    x * y + y * z + x * z = 70 := by

  have h4 : 0 < x * y := by
    apply mul_pos
    linarith
    linarith

  have h5 : 0 < y * z := by
    apply mul_pos
    linarith
    linarith

  have h6 : 0 < x * z := by
    apply mul_pos
    linarith
    linarith

  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]