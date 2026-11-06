import Mathlib

theorem algebra_150446 (x y : ℝ) :
    (2 * x + y + 8 ≤ 0 ∧ x ^ 4 + 2 * x ^ 2 * y ^ 2 + y ^ 4 + 9 - 10 * x ^ 2 - 10 * y ^ 2 = 8 * x * y) ↔
    (x = -3 ∧ y = -2) := by
  constructor
  · -- Forward direction: both conditions imply (x, y) = (-3, -2)
    rintro ⟨h1, h2⟩
    have h3 : (x - -3) ^ 2 + (y - -2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + 3), sq_nonneg (y + 2)]
    have hx1 : x - -3 = 0 := by
      nlinarith [sq_nonneg (x - -3), sq_nonneg (y - -2)]
    have hy1 : y - -2 = 0 := by
      nlinarith [sq_nonneg (x - -3), sq_nonneg (y - -2)]
    constructor
    · -- x = -3
      linarith
    · -- y = -2
      linarith
  · -- Backward direction: (x, y) = (-3, -2) implies both conditions
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Check inequality
      norm_num
    · -- Check equation
      norm_num