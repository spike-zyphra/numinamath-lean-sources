import Mathlib


theorem algebra_290555 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hsum : x + y = 2) :
    x^2 * y^2 * (x^2 + y^2) ≤ 2 ∧ (∃ x' y':ℝ, 0<x' ∧ 0<y' ∧ x'^2*y'^2 * (x'^2 + y'^2) = 2) := by

  have h1 : y = 2 - x := by linarith
  have h2 : x * y ≤ 1 := by
    rw [show y = 2 - x by linarith]
    nlinarith [sq_nonneg (x - 1)]
  
  constructor
  · -- Prove the main inequality: $x^2 * y^2 * (x^2 + y^2) ≤ 2$
    rw [show y = 2 - x by linarith]
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x * (2 - x) - 1), sq_nonneg (x * (2 - x)), sq_nonneg ((x - 1) * (x * (2 - x))), sq_nonneg (x ^ 2 - (2 - x) ^ 2), sq_nonneg (x * (2 - x) * (x - 1)), mul_pos hx (show (0 : ℝ) < 2 - x by nlinarith)]
  · -- Show existence of $x', y'$ with maximum value
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num