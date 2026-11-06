import Mathlib

theorem algebra_151737 (x : ℝ) :
    (3 * x ^ 4 + 13 * x ^ 3 + 20 * x ^ 2 + 17 * x + 7 = 0 ∧
     3 * x ^ 4 + x ^ 3 - 8 * x ^ 2 + 11 * x - 7 = 0) ↔
    x = -7 / 3 := by
  constructor
  · -- Forward direction: both equations hold implies x = -7/3
    rintro ⟨h₁, h₂⟩
    have h3 : 6 * x ^ 3 + 14 * x ^ 2 + 3 * x + 7 = 0 := by
      nlinarith
    have h4 : (3 * x + 7) * (2 * x ^ 2 + 1) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 7 / 3), sq_nonneg (x - 7 / 3)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where 3x + 7 = 0
      linarith
    · -- Case where 2x^2 + 1 = 0, which implies a contradiction
      nlinarith [sq_nonneg x]
  · -- Backward direction: x = -7/3 implies both equations
    intro h
    rw [h]
    constructor
    · -- Verify the first equation
      norm_num
    · -- Verify the second equation
      norm_num