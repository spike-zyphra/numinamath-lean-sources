import Mathlib

/- The lines $y=5x+3$, $y=-2x-25$ and $y=3x+k$ intersect at the same point. What is the value of $k$? -/
theorem algebra_16261 {k : ℝ} (h : ∃ x, 5 * x + 3 = -2 * x - 25 ∧ -2 * x - 25 = 3 * x + k) :
    k = -5 := by 
  obtain ⟨x, hx1, hx2⟩ := h
  linarith [hx1, hx2]