import Mathlib

theorem algebra_261200 (x : ℝ) : (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6 ↔
    x = -2 / 3 ∨ x = -5 / 3 := by
  constructor
  · -- Forward direction: if the equation holds, then x = -2/3 or x = -5/3
    intro h
    have h1 : (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) - 6 = 0 := by linarith
    have h2 : (x + 2 / 3) * (x + 5 / 3) = 0 := by
      nlinarith [sq_nonneg (6 * x + 7), sq_nonneg (x + 2 / 3), sq_nonneg (x + 5 / 3),
        sq_nonneg (x + 1 / 3)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · left
      linarith
    · right
      linarith
  · -- Backward direction: if x = -2/3 or x = -5/3, then the equation holds
    rintro (h | h)
    · -- Case x = -2/3
      rw [h]
      norm_num
    · -- Case x = -5/3
      rw [h]
      norm_num