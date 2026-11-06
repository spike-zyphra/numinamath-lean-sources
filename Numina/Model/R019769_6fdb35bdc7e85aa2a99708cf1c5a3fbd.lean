import Mathlib

theorem algebra_10713 (x y : ℝ) (h : (x - 3)^2 + 4 * (y - 1)^2 = 4) :
    (x + y - 3) / (x - y + 1) ≤ 1 ∧ (x + y - 3) / (x - y + 1) ≥ -1 := by
  have h1 : x - y + 1 ≠ 0 := by
    by_contra h1
    have h2 : y = x + 1 := by linarith
    rw [h2] at h
    nlinarith [sq_nonneg (x - 3 / 5), sq_nonneg (x + 3 / 5)]

  have h3 : 0 < x - y + 1 := by
    nlinarith [sq_nonneg (x - 3 - 2 * (y - 1)), sq_nonneg (2 * (x - 3) + 4 * (y - 1)), sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg ((x - (3 - 2 * (y - 1)))), sq_nonneg ((x - 3 + 2) + (y - 1)), sq_nonneg ((x - 3) - 2 * (y - 1)), sq_nonneg ((x - 3) + 2), sq_nonneg ((y - 1)), sq_nonneg ((x - y + 1) - 3)]
  
  constructor
  · -- Prove that (x + y - 3) / (x - y + 1) ≤ 1
    apply (div_le_iff (by linarith)).mpr
    nlinarith [sq_nonneg (x - 3 - 2 * (y - 1)), sq_nonneg (2 * (x - 3) + 4 * (y - 1)), sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg ((x - (3 - 2 * (y - 1)))), sq_nonneg ((x - 3 + 2) + (y - 1)), sq_nonneg ((x - 3) - 2 * (y - 1)), sq_nonneg ((x - 3) + 2), sq_nonneg ((y - 1)), sq_nonneg ((x - y + 1) - 3)]
  · -- Prove that (x + y - 3) / (x - y + 1) ≥ -1
    apply (le_div_iff (by linarith)).mpr
    nlinarith [sq_nonneg (x - 3 - 2 * (y - 1)), sq_nonneg (2 * (x - 3) + 4 * (y - 1)), sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg ((x - (3 - 2 * (y - 1)))), sq_nonneg ((x - 3 + 2) + (y - 1)), sq_nonneg ((x - 3) - 2 * (y - 1)), sq_nonneg ((x - 3) + 2), sq_nonneg ((y - 1)), sq_nonneg ((x - y + 1) - 3)]