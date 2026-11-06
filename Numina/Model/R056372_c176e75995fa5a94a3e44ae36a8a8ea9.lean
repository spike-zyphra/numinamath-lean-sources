import Mathlib

theorem algebra_18654 (x : ℝ) :
    x^4 + 2 * x^3 - 7 * x^2 - 8 * x + 12 = 0 ↔
    x = 1 ∨ x = 2 ∨ x = -2 ∨ x = -3 := by
  constructor
  · -- Forward direction: if the polynomial equals zero, then x is one of the roots
    intro h
    have h1 : x ^ 4 + 2 * x ^ 3 - 7 * x ^ 2 - 8 * x + 12 = (x - 1) * (x - 2) * (x + 2) * (x + 3) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.1 h) with h2 h3
    cases' (mul_eq_zero.1 h2) with h4 h5
    cases' (mul_eq_zero.1 h4) with h6 h7
    · -- Case 1: x - 1 = 0 so x = 1
      left
      linarith 
    · -- Case 2: x - 2 = 0 so x = 2
      right
      left
      linarith
    · -- Case 3: x + 2 = 0 so x = -2
      right
      right
      left
      linarith
    · -- Case 4: x + 3 = 0 so x = -3
      right
      right
      right
      linarith
  · -- Backward direction: if x is one of the roots, then the polynomial equals zero
    rintro (h | h | h | h)
    · -- x = 1
      rw [h]
      norm_num
    · -- x = 2
      rw [h]
      norm_num
    · -- x = -2
      rw [h]
      norm_num
    · -- x = -3
      rw [h]
      norm_num