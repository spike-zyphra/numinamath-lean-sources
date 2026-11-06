import Mathlib

open Real Set

theorem inequalities_12408 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (2 * x + y) + y / (x + 2 * y) ≤ 2 / 3 := by
  have h1 : 0 < 2 * x + y := by linarith
  have h2 : 0 < x + 2 * y := by linarith
  have h3 : 0 < 3 * (2 * x + y) * (x + 2 * y) := by positivity
  have h4 : x / (2 * x + y) + y / (x + 2 * y) - 2 / 3 ≤ 0 := by
    have h5 : x / (2 * x + y) + y / (x + 2 * y) - 2 / 3 =
        (3 * x * (x + 2 * y) + 3 * y * (2 * x + y) - 2 * (2 * x + y) * (x + 2 * y)) / (3 * (2 * x + y) * (x + 2 * y)) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonpos_of_nonpos_of_nonneg
    -- Show the numerator is nonpositive
    have h6 : 3 * x * (x + 2 * y) + 3 * y * (2 * x + y) - 2 * (2 * x + y) * (x + 2 * y) ≤ 0 := by
      nlinarith [sq_nonneg (x - y)]
    linarith
    -- Show the denominator is nonnegative
    positivity
  linarith [h4]