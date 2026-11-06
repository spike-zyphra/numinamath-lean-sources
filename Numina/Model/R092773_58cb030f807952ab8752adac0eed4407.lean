import Mathlib

theorem algebra_295817 (x : ℤ) : x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3 ↔ x = 3 := by
  constructor
  · -- Assume x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3 prove x = 3
    intro h
    have eqn : x^3 + (x + 1)^3 + (x + 2)^3 - (x + 3)^3 = 0 := by linarith
    have eqn_simpl : 2 * x^3 - 12 * x - 18 = 0 := by 
      ring_nf at eqn ⊢
      linarith
    -- Then we can factor the equation as (x - 3)(x^2 + 3 x + 3) = 0
    have eqn_simpl_2 : x^3 - 6 * x - 9 = 0 := by 
      linarith
    -- We can factor the equation as (x - 3)(x^2 + 3 x + 3) = 0 
    have h_eq : (x - 3) * (x^2 + 3 * x + 3) = 0 := by 
      ring_nf at eqn_simpl_2 ⊢
      linarith
    cases' (mul_eq_zero.mp h_eq) with h1 h2
    · -- Case where $x - 3 = 0$
      linarith
    · -- Case where $x^2 + 3x + 3 = 0$
      have h_eq : x^2 + 3 * x + 3 = 0 := h2
      have h1 : (2 * x + 3)^2 = -3 := by 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 2), sq_nonneg (x + 3)]
      have h2 : (2 * x + 3)^2 ≥ 0 := sq_nonneg (2 * x + 3)
      linarith
  · -- Assume x = 3 prove x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3
    intro h_eq
    rw [h_eq]
    norm_num