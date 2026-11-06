import Mathlib

theorem algebra_164944 (y : ℝ) (hy : ∃ x, y + x = (y - x)^2 + 3 * (y - x) + 3) :
    y ≥ -1 / 2 := by 
  rcases hy with ⟨x, hx⟩
  nlinarith [sq_nonneg (y - x + 2), sq_nonneg (x - (y + 2)), sq_nonneg ((y - x) + 2), sq_nonneg (y + 1 / 2), sq_nonneg (x + 2 - y)]