import Mathlib

theorem algebra_309458 {a b : ℝ} (h : a^3 + b^3 + 3 * a * b = 1) :
    a + b = 1 ∨ a + b = -2 := by
  have h1 : (a + b) ^ 3 - 3 * a * b * (a + b) + 3 * a * b = 1 := by
    have h_a3b3 : a^3 + b^3 = (a + b)^3 - 3 * a * b * (a + b) := by
      ring
    nlinarith [h_a3b3, h]

  have h2 : (a + b - 1) * ((a + b) ^ 2 + (a + b) + 1 - 3 * (a * b)) = 0 := by
    have h_eq : (a + b) ^ 3 - 3 * a * b * (a + b) + 3 * a * b - 1 = 0 := by
      linarith [h1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1)]

  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case $a + b - 1 = 0$
    left
    linarith
  · -- Case $(a + b) ^ 2 + (a + b) + 1 - 3 * (a * b) = 0$
    have h4' : (a + b) ^ 2 + (a + b) + 1 - 3 * (a * b) = 0 := by 
      nlinarith
    have h5 : 0 ≥ (a + b + 2)^2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    have eq_zero : a + b + 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1)]
    right
    linarith