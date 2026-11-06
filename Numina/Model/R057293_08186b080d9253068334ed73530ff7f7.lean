import Mathlib

theorem algebra_195909 (x y : ℝ) :
    (x - 5)^2 + (y - 6)^2 + (x - y)^2 = 1 / 3 ↔
    (x = 5 + 1 / 3 ∧ y = 5 + 2 / 3) := by
  constructor
  · -- Forward direction: If equation holds, then get x and y.
    intro h
    have h1 : (x - 16 / 3) ^ 2 + (y - 17 / 3) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - 16 / 3), sq_nonneg (y - 17 / 3), sq_nonneg (4 * x - 2 * y - 10), sq_nonneg (-2 * x + 4 * y - 12)]
    have hx1 : x - 16 / 3 = 0 := by
      nlinarith [sq_nonneg (x - 16 / 3), sq_nonneg (y - 17 / 3)]
    have hx2 : x = 16 / 3 := by
      linarith
    have hy1 : y - 17 / 3 = 0 := by
      nlinarith [sq_nonneg (x - 16 / 3), sq_nonneg (y - 17 / 3)]
    have hy2 : y = 17 / 3 := by
      linarith
    constructor
    · -- Show x = 5 + 1/3.
      linarith
      -- x = 16/3 ≍ 5 + 1/3.
    · -- Show y = 5 + 2/3.
      linarith
      -- y = 17/3 ≉ 5 + 2/3.
  · -- Backward direction: If x and y, then equation holds.
    rintro ⟨hx, hy⟩
    -- Using given x and y satisfy the equation.
    have hx1 : x = 16 / 3 := by
      linarith
      -- 5 + 1/3 ≉ 16/3.
    have hy1 : y = 17 / 3 := by
      linarith
      -- 5 + 2/3 ≉ 17/3
    rw [hx1, hy1]
    -- Verify given x and y the equation.
    norm_num