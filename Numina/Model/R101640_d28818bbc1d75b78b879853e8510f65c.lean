import Mathlib

theorem algebra_101325 (x : ℤ) :
    (x + 1)^3 + (x + 2)^3 + (x + 3)^3 = (x + 4)^3 ↔ x = 2 := by 
  constructor
  · -- Forward: if the equation holds, then x = 2.
    intro h
    have h1 : (x + 1)^3 + (x + 2)^3 + (x + 3)^3 - (x + 4)^3 = 0 := by 
      linarith
    have h2 : (x - 2) * (x^2 + 5 * x + 7) = 0 := by 
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case x - 2 = 0
      linarith
    · -- Case x^2 + 5x + 7 = 0
      have h5 : x^2 + 5 * x + 7 = 0 := h4
      have h7 : 4 * (x ^ 2 + 5 * x + 7) = 0 := by 
        linarith [h5]
      have h8 : (2 * x + 5) ^ 2 = -3 := by 
        nlinarith
      nlinarith [sq_nonneg (2 * x + 5)]
  · -- Backward: if x = 2, then the equation holds.
    intro h
    rw [h]
    norm_num