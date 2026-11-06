import Mathlib

theorem algebra_316470 (x y z : ℝ) (h : x^2 + y^2 + z^2 - x * y - y * z - z * x = 27) :
    abs (y - z) ≤ 6 := by 
  have h1 : -3 * (y - z) ^ 2 + 108 ≥ 0 := by
    nlinarith [sq_nonneg (x - (y + z) / 2), sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z)]
  have h2 : (y - z) ^ 2 ≤ 36 := by
    nlinarith
  have h3 : abs (y - z) ≤ 6 := by
    have h4 : (y - z) ^ 2 ≤ 36 := h2
    have h5 : -6 ≤ y - z := by
      nlinarith [sq_nonneg (y - z)]
    have h6 : y - z ≤ 6 := by
      nlinarith [sq_nonneg (y - z)]
    apply abs_le.mpr
    constructor <;> linarith
  exact h3