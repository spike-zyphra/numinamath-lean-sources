import Mathlib

theorem algebra_213382 (a b c d : ℤ) (h₀ : a > b ∧ b > c ∧ c > d ∧ d ≥ -2021)
    (h₁ : (a + b) * (d + a) = (c + d) * (b + c)) (h₂ : b + c ≠ 0) (h₃ : d + a ≠ 0) :
    a * c ≤ 510050 := by
  rcases h₀ with ⟨h4, h5, h6, h7⟩
  have h8 : (a - c) * (a + b + c + d) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- case a - c = 0
    -- which contradicts with a > b > c
    have h10 : a = c := by linarith
    nlinarith
  · -- case a + b + c + d = 0
    -- which means d = - (a + b + c)
    have h11 : a + b + c + d = 0 := by linarith
    -- which means a + b + c ≤ 2021
    have h14 : a + b + c ≤ 2021 := by
      nlinarith
    -- which means a > c
    have h13 : a > c := by linarith
    nlinarith [sq_nonneg (a - 1010), sq_nonneg (c - 1010), sq_nonneg (b - 1011), sq_nonneg (d + 2021)]