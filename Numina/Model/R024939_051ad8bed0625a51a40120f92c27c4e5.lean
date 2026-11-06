import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_298342 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hsum : x + y + z = 1) :
  (3 * x^2 - x) / (1 + x^2) + (3 * y^2 - y) / (1 + y^2) +
  (3 * z^2 - z) / (1 + z^2) ≥ 0 := by
  have h1 : 0 < x := hx
  have h2 : 0 < y := hy
  have h3 : 0 < z := hz
  have h4 : x + y + z = 1 := hsum
  have hx2 : 1 + x^2 > 0 := by nlinarith
  have hy2 : 1 + y^2 > 0 := by nlinarith
  have hz2 : 1 + z^2 > 0 := by nlinarith
  have h5 : (3 * x^2 - x) / (1 + x^2) + (3 * y^2 - y) / (1 + y^2) + (3 * z^2 - z) / (1 + z^2) =
      ( (3 * x^2 - x) * (1 + y^2) * (1 + z^2) + (3 * y^2 - y) * (1 + x^2) * (1 + z^2) + (3 * z^2 - z) * (1 + x^2) * (1 + y^2) ) / ( (1 + x^2) * (1 + y^2) * (1 + z^2) ) := by
    field_simp
    ring
  rw [h5] at *
  have h6 : ( (3 * x^2 - x) * (1 + y^2) * (1 + z^2) + (3 * y^2 - y) * (1 + x^2) * (1 + z^2) + (3 * z^2 - z) * (1 + x^2) * (1 + y^2) ) / ( (1 + x^2) * (1 + y^2) * (1 + z^2) ) ≥ 0 := by
    apply div_nonneg
    -- Show the numerator is non-negative
    have h7 : (3 * x^2 - x) * (1 + y^2) * (1 + z^2) + (3 * y^2 - y) * (1 + x^2) * (1 + z^2) + (3 * z^2 - z) * (1 + x^2) * (1 + y^2) ≥ 0 := by
      have hx3 : x * y > 0 := by nlinarith
      have hx4 : x * z > 0 := by nlinarith
      have hx5 : y * z > 0 := by nlinarith
      -- Substitute z = 1 - x - y
      have h7 : z = 1 - x - y := by nlinarith
      rw [h7]
      -- Now we simplified to two variables.
      nlinarith [sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg ((1 - x - y) - 1/3),
        mul_pos h1 h2, mul_pos h1 (show 0 < (1 - x - y : ℝ) by nlinarith),
        mul_pos h2 (show 0 < (1 - x - y : ℝ) by nlinarith),
        sq_nonneg (x * y - 1/9), sq_nonneg (x * (1 - x - y) - 1/9),
        sq_nonneg (y * (1 - x - y) - 1/9)]
    linarith
    -- Show the denominator is positive
    positivity
  linarith