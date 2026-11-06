import Mathlib

open Real

theorem inequalities_114622 (x : ℝ) (hx : x ≥ 0) :
    1 + x^2 + x^6 + x^8 ≥ 4 * x^4 ∧
    (1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1) := by
  constructor
  · -- First part: prove the inequality
    nlinarith [sq_nonneg (x^4 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x^3 - x), sq_nonneg (x - 1),
      pow_two_nonneg (x^2 - 1), pow_two_nonneg (x^3 - x), 
      sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - x^4),
      mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ x by linarith)]
  · -- Second part: characterized the equality
    constructor
    · -- Forward direction: if equality holds, then x = 1
      intro h
      have h1 : 1 + x^2 + x^6 + x^8 = 4 * x^4 := h
      have h4 : x^2 = 1 := by 
        nlinarith [sq_nonneg (x^4 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x^3 - x), sq_nonneg (x - 1),
          pow_two_nonneg (x^2 - 1), pow_two_nonneg (x^3 - x), 
          sq_nonneg (x^4 - x^2), sq_nonneg (x^2 - x^4),
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ x by linarith)]
      have h6 : x = 1 := by 
        nlinarith [sq_nonneg (x - 1)]
      exact h6
    · -- Backward direction: if x = 1, then equality holds
      intro h
      rw [h]
      norm_num