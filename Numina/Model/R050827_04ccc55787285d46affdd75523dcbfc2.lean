import Mathlib

theorem algebra_314649 (x : ℝ) (hx : x^4 + x^2 + 1 ≠ 0) :
    (4 * x^2 + 2 * x + 6) / (x^4 + x^2 + 1) =
    (x + 2) / (x^2 + x + 1) + (-x + 4) / (x^2 - x + 1) := by 
  have h1 : x^4 + x^2 + 1 = (x^2 + x + 1) * (x^2 - x + 1) := by
    nlinarith [sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 + x)]
  rw [h1]
  field_simp [(show (x^2 + x + 1 : ℝ) ≠ 0 by
      by_contra h
      have : x^4 + x^2 + 1 = 0 := by
        nlinarith [sq_nonneg (x^2 + x), sq_nonneg (x ^ 2 - x + 1), sq_nonneg (x + 2), sq_nonneg (x - 1)]
        all_goals nlinarith
      contradiction
  ), (show (x^2 - x + 1 : ℝ) ≠ 0 by
      by_contra h
      have : x^4 + x^2 + 1 = 0 := by
        nlinarith [sq_nonneg (x^2 + x), sq_nonneg (x ^ 2 - x + 1), sq_nonneg (x + 2), sq_nonneg (x - 1)]
        all_goals nlinarith
      contradiction
  ), hx]
  ring
  all_goals ring_nf <;> nlinarith