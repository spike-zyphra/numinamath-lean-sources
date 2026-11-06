import Mathlib

theorem algebra_196244 (x y : ℝ) :
    (x - 9)^2 + (y - 10)^2 + (x - y)^2 = 1 / 3 ↔
    x = 9 + 1 / 3 ∧ y = 9 + 2 / 3 := by 
  constructor
  · -- First, we prove the forward direction: if the equation holds, then x = 9 + 1/3 ∧ y = 9 + 2/3
    intro h
    have h1 : (x - (28 / 3)) ^ 2 + (y - (29 / 3)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 9), sq_nonneg (y - 10)]
    have hx : x - (28 / 3) = 0 := by
      nlinarith [sq_nonneg (x - (28 / 3)), sq_nonneg (y - (29 / 3))]
    have hy : y - (29 / 3) = 0 := by
      nlinarith [sq_nonneg (x - (28 / 3)), sq_nonneg (y - (29 / 3))]
    constructor
    · -- Show x = 9 + 1/3
      linarith [hx]
    · -- Show y = 9 + 2/3
      linarith [hy]
  · -- Now for the reverse direction: if x = 9 + 1/3 ∧ y = 9 + 2/3, then the equation holds
    rintro ⟨rfl, rfl⟩
    norm_num