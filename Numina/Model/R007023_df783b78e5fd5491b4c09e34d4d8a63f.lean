import Mathlib

theorem algebra_192279 (a b c : ℝ) (ha : a ≠ 0)
(h1 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + c * x + a = 0 ∧ c * x ^ 2 + a * x + b = 0) :
    b + c + a = 0 := by 
  rcases h1 with ⟨x, h1, h2, h3⟩
  have h4 : (a + b + c) * (x ^ 2 + x + 1) = 0 := by 
    linarith
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- case where h5 is true, so a + b + c = 0, trivial to show b + c + a = 0 
    linarith
  · -- case where h6 is true, so x^2 + x + 1 = 0, need to show it's impossible.
    have h7 : x ^ 2 + x + 1 ≠ 0 := by
      have h8 : x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h8 : x ^ 2 + x + 1 = 0 := by
      linarith
    contradiction