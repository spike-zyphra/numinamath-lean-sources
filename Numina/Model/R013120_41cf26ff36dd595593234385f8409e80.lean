import Mathlib

theorem inequalities_2647
    (x y z : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z)
    (hxyz : x * y * z = 1) :
    (1 / (2 * x + 2)) + (1 / (2 * y + 2)) + (1 / (2 * z + 2)) ≥
    (1 / (2 + x + y)) + (1 / (2 + y + z)) + (1 / (2 + z + x)) := by

  have h1 : 0 < 2 * x + 2 := by nlinarith
  have h2 : 0 < 2 * y + 2 := by nlinarith
  have h3 : 0 < 2 * z + 2 := by nlinarith
  have h4 : 0 < 2 + x + y := by nlinarith
  have h5 : 0 < 2 + y + z := by nlinarith
  have h6 : 0 < 2 + z + x := by nlinarith

  have h7 : (1 / (2 * x + 2)) + (1 / (2 * y + 2)) + (1 / (2 * z + 2)) - ((1 / (2 + x + y)) + (1 / (2 + y + z)) + (1 / (2 + z + x))) ≥ 0 := by
    have h8 : ((1 / (2 * x + 2)) + (1 / (2 * y + 2)) + (1 / (2 * z + 2)) - ((1 / (2 + x + y)) + (1 / (2 + y + z)) + (1 / (2 + z + x))) ) =
        (( (2 * y + 2) * (2 * z + 2) * (2 + x + y) * (2 + y + z) * (2 + z + x) + (2 * x + 2) * (2 * z + 2) * (2 + x + y) * (2 + y + z) * (2 + z + x) + (2 * x + 2) * (2 * y + 2) * (2 + x + y) * (2 + y + z) * (2 + z + x) - ( (2 * x + 2) * (2 * y + 2) * (2 * z + 2) * (2 + y + z) * (2 + z + x) + (2 * x + 2) * (2 * y + 2) * (2 * z + 2) * (2 + x + y) * (2 + z + x) + (2 * x + 2) * (2 * y + 2) * (2 * z + 2) * (2 + x + y) * (2 + y + z) )) / ((2 * x + 2) * (2 * y + 2) * (2 * z + 2) * (2 + x + y) * (2 + y + z) * (2 + z + x)) ) := by
      field_simp
      ring
    rw [h8] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x * y + y * z + z * x - 3), sq_nonneg (x + y + z - 3),
      mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz, hxyz]
    positivity

  linarith