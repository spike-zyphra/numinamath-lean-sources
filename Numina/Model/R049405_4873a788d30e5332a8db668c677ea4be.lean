import Mathlib

theorem algebra_219951 (x : ℝ) (hx : x^4 - 2 * x^2 - 400 * x = 9999) :
    x = 11 ∨ x = -9 := by
  have h_eq : x^4 - 2 * x^2 - 400 * x - 9999 = 0 := by
    linarith
  have h1 : (x - 11) * (x + 9) * (x^2 + 2 * x + 101) = 0 := by 
    nlinarith [sq_nonneg (x^2), sq_nonneg (x - 11), sq_nonneg (x + 9), sq_nonneg (x^2 - 2 * x - 99), sq_nonneg (x^2 + 2 * x + 101)]
  
  -- Now, we have factored the polynomial, so either x - 11 = 0, x + 9 = 0, or x^2 + 2x + 101 = 0
  cases (mul_eq_zero.mp h1) with
  | inl h1l =>
    cases (mul_eq_zero.mp h1l) with
    | inl h1ll =>
      -- Case where x - 11 = 0, so x = 11
      left
      linarith
    | inr h1lr =>
      -- Case where x + 9 = 0, so x = -9
      right
      linarith
  | inr h1r =>
    -- Case where x^2 + 2x + 101 = 0
    have : x^2 + 2 * x + 101 > 0 := by 
      nlinarith [sq_nonneg (x + 1)]
    have : x^2 + 2 * x + 101 = 0 := by linarith
    nlinarith -- This will generate a contradiction because x^2 + 2x + 101 > 0