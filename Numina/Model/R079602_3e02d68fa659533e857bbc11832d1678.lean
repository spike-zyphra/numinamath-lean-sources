import Mathlib

theorem algebra_599101 (x y z : ℝ) :
    x^2 + y^2 + z^2 = 9 / 4 ∧ -8 * x + 6 * y - 24 * z = 39 ↔
    x = -6 / 13 ∧ y = 9 / 26 ∧ z = -18 / 13 := by
  constructor
  · -- Forward direction: If (x^2 + y^2 + z^2) = 9/4 and -8x + 6y - 24z = 39, then (x, y, z) = (-6/13, 9/26, -18/13)
    rintro ⟨h1, h2⟩
    have h3 : (x + 6 / 13) ^ 2 + (y - 9 / 26) ^ 2 + (z + 18 / 13) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
    have hx : (x + 6 / 13) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
    have hy : (y - 9 / 26) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
    have hz : (z + 18 / 13) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13)]
    have hx1 : x + 6 / 13 = 0 := by
      rwa [sq_eq_zero_iff] at hx
    have hy1 : y - 9 / 26 = 0 := by
      rwa [sq_eq_zero_iff] at hy
    have hz1 : z + 18 / 13 = 0 := by
      rwa [sq_eq_zero_iff] at hz
    constructor
    · -- Solving for x
      linarith
    constructor
    · -- Solving for y
      linarith
    · -- Solving for z
      linarith
  · -- Backward direction: If (x, y, z) = (-6/13, 9/26, -18/13), then (x^2 + y^2 + z^2) = 9/4 and -8x + 6y - 24z = 39
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Show x^2 + y^2 + z^2 = 9 / 4
      norm_num
    · -- Show -8 * x + 6 * y - 24 * z = 39
      norm_num