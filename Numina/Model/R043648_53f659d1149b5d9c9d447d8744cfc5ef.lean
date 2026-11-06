import Mathlib

theorem algebra_184505 (x : ℤ) :
    ∃ y : ℤ, y^2 = x^2 + 19 * x + 95 ↔ x = -14 ∨ x = -5 := by
  use 5
  constructor
  · -- Assume $y^2 = x^2 + 19 * x + 95$, prove $x = -14 ∨ x = -5$
    intro h
    have h1 : x^2 + 19 * x + 95 = 25 := by
      linarith
    have h2 : x^2 + 19 * x + 70 = 0 := by
      linarith
    have h3 : (x + 14) * (x + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case $x + 14 = 0$, so $x = -14$
      left
      linarith
    · -- Case $x + 5 = 0$, so $x = -5$
      right
      linarith
  · -- Assume $x = -14 ∨ x = -5$, prove $y^2 = x^2 + 19 * x + 95$
    rintro (h | h)
    · -- Case $x = -14$
      rw [h]
      norm_num
    · -- Case $x = -5$
      rw [h]
      norm_num