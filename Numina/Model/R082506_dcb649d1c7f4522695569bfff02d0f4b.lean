import Mathlib

theorem algebra_99288 (x y : ℝ) :
    x^2 + (1 - y)^2 + (x - y)^2 = 1 / 3 ↔ x = 1 / 3 ∧ y = 2 / 3 := by
  constructor
  · -- Forward direction: If the equation holds, then (x, y) = (1/3, 2/3)
    intro h
    have h_eq : (x - 1/3)^2 + (y - 2/3)^2 = 0 := by
      nlinarith [sq_nonneg (x - 1/3), sq_nonneg (y - 2/3), sq_nonneg (x - y), sq_nonneg (x - 1/3), sq_nonneg (y - 2/3)]
    have hx : x - 1/3 = 0 := by
      nlinarith [sq_nonneg (x - 1/3), sq_nonneg (y - 2/3)]
    have hy : y - 2/3 = 0 := by
      nlinarith [sq_nonneg (x - 1/3), sq_nonneg (y - 2/3)]
    constructor
    · -- Solving for x
      linarith
    · -- Solving for y
      linarith
  · -- Backward direction: If (x, y) = (1/3, 2/3), then the equation holds
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num