import Mathlib

theorem algebra_319458 (x y : ℤ) : x^2 + y^2 - 14 * x + 2 * y + 50 = 0 ↔ (x = 7 ∧ y = -1) := by
  constructor
  · -- Forward direction: If the equation holds, then (x = 7 ∧ y = -1)
    intro h
    have h1 : (x - 7)^2 + (y + 1)^2 = 0 := by
      nlinarith
    have h2 : (x - 7)^2 = 0 := by
      linarith [sq_nonneg (x - 7), sq_nonneg (y + 1)]
    have h3 : (y + 1)^2 = 0 := by
      linarith [sq_nonneg (x - 7), sq_nonneg (y + 1)]
    have hx : x = 7 := by
      nlinarith
    have hy : y = -1 := by
      nlinarith
    exact ⟨hx, hy⟩
  · -- Backward direction: If (x = 7 ∧ y = -1), then the equation holds
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num