import Mathlib

theorem algebra_2940 (x : ℤ) :
    3*x^2-8*x-35=0 ↔ x=5 := by
  constructor
  · -- Assume 3*x^2-8*x-35=0, we need to prove x=5
    intro h
    have h1 : 3 * x^2 - 8 * x - 35 = 0 := h
    have h3 : (x - 5) * (3 * x + 7) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where x - 5 = 0, so x = 5
      linarith
    · -- Case where 3x + 7 = 0, so 3x = -7
      have h6 : 3 * x = -7 := by linarith
      omega
  · -- Assume x=5, prove 3*x^2-8*x-35=0
    intro h_eq
    rw [h_eq]
    norm_num