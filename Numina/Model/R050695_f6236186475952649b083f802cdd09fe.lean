import Mathlib

theorem algebra_196659 (x y : ℝ) :
    (x - 14)^2 + (y - 15)^2 + (x - y)^2 = 1 / 3 ↔
    (x = 14 + 1 / 3 ∧ y = 14 + 2 / 3) := by
  constructor
  · -- Assume (x - 14)^2 + (y - 15)^2 + (x - y)^2 = 1/3, prove x = 14 + 1/3 ∧ y = 14 + 2/3
    intro h
    have h1 : (x - 14 - 1 / 3) ^ 2 + (y - 14 - 2 / 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 14 - 1 / 3), sq_nonneg (y - 14 - 2 / 3), sq_nonneg (x - y), sq_nonneg (x - 14 - 1 / 3), sq_nonneg (y - 15 + 1 / 3)]
    have hx1 : (x - 14 - 1 / 3) ^ 2 = 0 := by
      linarith [sq_nonneg (x - 14 - 1 / 3), sq_nonneg (y - 14 - 2 / 3)]
    have hy1 : (y - 14 - 2 / 3) ^ 2 = 0 := by
      linarith [sq_nonneg (x - 14 - 1 / 3), sq_nonneg (y - 14 - 2 / 3)]
    constructor
    · -- Prove x = 14 + 1/3
      nlinarith [sq_nonneg (x - 14 - 1 / 3), sq_nonneg (y - 14 - 2 / 3)]
    · -- Prove y = 14 + 2/3
      nlinarith [sq_nonneg (x - 14 - 1 / 3), sq_nonneg (y - 14 - 2 / 3)]
  · -- Assume x = 14 + 1/3 ∧ y = 14 + 2/3, prove (x - 14)^2 + (y - 15)^2 + (x - y)^2 = 1/3
    rintro ⟨rfl, rfl⟩
    norm_num
    all_goals norm_num