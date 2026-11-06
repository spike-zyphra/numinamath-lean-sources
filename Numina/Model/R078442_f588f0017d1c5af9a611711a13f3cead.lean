import Mathlib

theorem algebra_207902 (x : Fin 3 → ℝ) (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 0 * x 1 + x 1 * x 2 = 2) :
    abs (x 1) ≤ 2 := by 
  have h1 : (x 0 + x 1 / 2) ^ 2 + (x 2 + x 1 / 2) ^ 2 + (x 1) ^ 2 / 2 = 2 := by
    nlinarith
  have h2 : (x 1) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (x 0 + x 1 / 2), sq_nonneg (x 2 + x 1 / 2)]
  have h4 : -2 ≤ x 1 ∧ x 1 ≤ 2 := by
    constructor
    · nlinarith [sq_nonneg (x 1), h2]
    · nlinarith [sq_nonneg (x 1), h2]
  apply abs_le.mpr 
  constructor <;> linarith