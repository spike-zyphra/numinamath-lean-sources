import Mathlib

theorem algebra_170289 (a : ℝ) :
    (∀ x : ℝ, a * x^2 - 7 * x + 4 * a < 0) ↔ a < -7 / 4 := by
  constructor
  · -- Assume that for all real numbers x, a * x^2 -7 *x + 4 *a < 0, then a < -7/4.
    intro h
    have ha1 : a < 0 := by
      have h1 := h 0
      linarith 
    by_contra h3
    push_neg at h3
    have h4 := h (-2)
    nlinarith
  · -- Assume that a < -7 / 4, prove that ∀ x : ℝ, a * x ^ 2 - 7 * x + 4 * a < 0.
    intro ha x
    have ha1 : a < 0 := by linarith
    have ha2 : a ^ 2 > 49 / 16 := by nlinarith 
    nlinarith [sq_nonneg (a * x + 7 / 2), sq_nonneg (x * a + 7 / 4), sq_nonneg (x - 14 / 4), sq_nonneg (a + 7 / 4), sq_nonneg (x * (a + 7 / 4)), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_pos_of_neg (show a < 0 by linarith), sq_nonneg (x * a + 7 / 2 * (1 / a)), sq_nonneg ((a * x) + 7 / 4)]