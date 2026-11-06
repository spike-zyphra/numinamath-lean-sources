import Mathlib

theorem algebra_3109 (x : ℝ) (hx : x > 5) :
    1 / ((x ^ 2 - 3 * x + 2) : ℝ) + 1 / ((x ^ 2 - 5 * x + 6) : ℝ) +
    1 / ((x ^ 2 - 7 * x + 12) : ℝ) + 1 / ((x ^ 2 - 9 * x + 20) : ℝ) =
    4 / ((x ^ 2 - 6 * x + 5) : ℝ) := by
  have h1 : x ^ 2 - 3 * x + 2 ≠ 0 := by
    nlinarith
  have h2 : x ^ 2 - 5 * x + 6 ≠ 0 := by
    nlinarith
  have h3 : x ^ 2 - 7 * x + 12 ≠ 0 := by
    nlinarith
  have h4 : x ^ 2 - 9 * x + 20 ≠ 0 := by
    nlinarith
  have h5 : x ^ 2 - 6 * x + 5 ≠ 0 := by
    nlinarith
  field_simp [h1, h2, h3, h4, h5]
  ring