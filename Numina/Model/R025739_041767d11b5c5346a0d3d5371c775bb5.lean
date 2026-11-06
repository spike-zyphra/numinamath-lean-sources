import Mathlib

theorem algebra_187977 (x : ℝ) (h : (x + 3) ^ 4 + (x + 5) ^ 4 = 16) :
    x = -3 ∨ x = -5 := by
  have h2 : (x + 4 - 1) ^ 4 + (x + 4 + 1) ^ 4 = 16 := by 
    ring_nf at h ⊢
    nlinarith
  have h3 : (x + 4) ^ 2 = 1 := by
    nlinarith [sq_nonneg ((x + 4) ^ 2 - 1), sq_nonneg ((x + 4) ^ 2), sq_nonneg ((x + 4) ^ 2 - 1), sq_nonneg ((x + 4) + 1), sq_nonneg ((x + 4) - 1), sq_nonneg ((x + 4) ^ 2 - 1)]
  have h4 : (x + 4 - 1) * (x + 4 + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where $x + 4 - 1 = 0$, i.e., $x = -3$
    left
    linarith
  · -- Case where $x + 4 + 1 = 0$, i.e., $x = -5$
    right
    linarith