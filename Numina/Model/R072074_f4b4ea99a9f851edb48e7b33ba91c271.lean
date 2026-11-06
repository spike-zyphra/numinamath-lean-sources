import Mathlib

theorem algebra_320737 (x : ℝ) :
    (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6 ↔ x = -2 / 3 ∨ x = -5 / 3 := by
  constructor
  · -- Assume $(6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6$, prove $x = -2 / 3 ∨ x = -5 / 3$
    intro h
    have h_eq : (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) - 6 = 0 := by linarith 
    have h_eq2 : (x + 2 / 3) * (x + 5 / 3) = 0 := by 
      nlinarith [sq_nonneg (6 * x + 7), sq_nonneg (3 * x + 4), sq_nonneg (x + 1), sq_nonneg (6 * x + 4), sq_nonneg (3 * x + 5)]
    cases' (mul_eq_zero.mp h_eq2) with h1 h2
    · -- Case where $x + 2/3 = 0$
      left
      linarith
    · -- Case where $x + 5/3 = 0$
      right
      linarith
  · -- Assume $x = -2/3 ∨ x = -5/3$, prove $(6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6$
    rintro (h | h)
    · -- Case x = -2/3
      rw [h]
      norm_num
    · -- Case x = -5/3
      rw [h]
      norm_num