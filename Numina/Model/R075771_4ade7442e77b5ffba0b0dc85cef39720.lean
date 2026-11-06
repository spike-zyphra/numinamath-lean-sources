import Mathlib

theorem algebra_6920 (x y : ℝ) :
    5*x^2 + 16*x*y - 6*x + 29*y^2 + 12*y + 9 = 0 ↔ (x = 5/3 ∧ y = -2/3) := by
  constructor
  · -- Forward direction: equation implies the solution
    intro h
    have h1 : (x - 5/3)^2 + (y + 2/3)^2 = 0 := by
      nlinarith [sq_nonneg (x - 5/3), sq_nonneg (y + 2/3), sq_nonneg (x + (8 * y - 3) / 5), sq_nonneg (9 * y + 6)]
    have hx1 : x - 5/3 = 0 := by
      nlinarith [sq_nonneg (x - 5/3), sq_nonneg (y + 2/3)]
    have hy1 : y + 2/3 = 0 := by
      nlinarith [sq_nonneg (x - 5/3), sq_nonneg (y + 2/3)]
    constructor
    · linarith [hx1]
    · linarith [hy1]
  · -- Backward direction: solution implies the equation
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num