import Mathlib

theorem algebra_101603 (x : ℤ) :
    x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3 ↔ x = 3 := by 
  constructor
  · -- Forward direction: if the equation holds, then x = 3
    intro h
    have h1 : x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3 := h
    have eq1 : x^3 - 6 * x - 9 = 0 := by
      ring_nf at h1
      linarith 
    have eq : (x - 3) * (x ^ 2 + 3 * x + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq) with h3 h4
    · -- Case where x - 3 = 0, so x = 3 
      linarith
    · -- Case where x^2 + 3x + 3 = 0, show it's impossible over integers
      have h5 : x^2 + 3 * x + 3 = 0 := by
        nlinarith 
      have h6 : x ≥ -2 := by
        nlinarith [sq_nonneg (x + 1)]
      have h7 : x ≤ 1 := by
        nlinarith [sq_nonneg (x + 1)]
      interval_cases x <;> omega
  · -- Backward direction: if x = 3, then the equation holds
    intro h
    rw [h]
    norm_num