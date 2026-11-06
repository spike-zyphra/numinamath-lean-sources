import Mathlib

theorem algebra_75566 (y : ℝ) :
    (∃ x, y + x = (y - x)^2 + 3 * (y - x) + 3) ↔ y ≥ -1 / 2 := by
  constructor
  · -- Forward direction: existence implies bound
    rintro ⟨x, hx⟩
    nlinarith [sq_nonneg ((y - x) + 2), sq_nonneg ((y - x) + 1), sq_nonneg (x - (y + 1 / 2)), sq_nonneg (y + 1 / 2)]
  · -- Backward direction: bound implies existence
    intro hy
    use 2 + y - Real.sqrt (2 * y + 1)
    have h1 : 0 ≤ (2 * y + 1) := by nlinarith
    have h2 : (2 * y + 1) = (Real.sqrt (2 * y + 1))^2 := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (2 * y + 1), Real.sq_sqrt (show 0 ≤ (2 * y + 1 : ℝ) by nlinarith), sq_nonneg (Real.sqrt (2 * y + 1) - 1)]