import Mathlib

theorem algebra_221760 (x : ℝ) (hx : x ≠ 0) (h : x^6 - 19 * x^3 = 216) :
    x = 3 ∨ x = -2 := by
  have h1 : x^6 - 19 * x^3 - 216 = 0 := by linarith
  have h2 : (x^3) ^ 2 - 19 * (x^3) - 216 = 0 := by
    nlinarith
  have h3 : (x^3 - 27) * (x^3 + 8) = 0 := by
    nlinarith [h2]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case where $x^3 - 27 = 0$
    have h6 : x^3 = 27 := by linarith
    have h7 : x^3 - 27 = 0 := by linarith [h6]
    have h8 : (x - 3) * (x^2 + 3 * x + 9) = 0 := by 
      nlinarith [h7]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case where $x - 3 = 0$
      left
      linarith
    · -- Case where $x^2 + 3 * x + 9 = 0$
      exfalso
      have h11 : x ^ 2 + 3 * x + 9 > 0 := by
        nlinarith [sq_nonneg (x + 3 / 2)]
      have h12 : x ^ 2 + 3 * x + 9 = 0 := by linarith [h10]
      nlinarith [h11, h12]
  · -- Case where $x^3 + 8 = 0$
    have h8 : x^3 = -8 := by linarith
    have h9 : x^3 + 8 = 0 := by linarith [h8]
    have h10 : (x + 2) * (x^2 - 2 * x + 4) = 0 := by 
      nlinarith [h9]
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- Case where $x + 2 = 0$
      right
      linarith
    · -- Case where $x^2 - 2 * x + 4 = 0$
      exfalso
      have h13 : x ^ 2 - 2 * x + 4 > 0 := by
        nlinarith [sq_nonneg (x - 1)]
      have h14 : x ^ 2 - 2 * x + 4 = 0 := by linarith [h12]
      nlinarith [h13, h14]