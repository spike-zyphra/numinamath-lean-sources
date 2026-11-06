import Mathlib

theorem algebra_174813 (a b c : ℤ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c) :
    4 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2 ≥ 8 := by
  have h3 : (a - b) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h4
    apply h₀
    linarith
  have h4 : (a - c) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h5
    apply h₁
    linarith
  have h5 : (b - c) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h6
    apply h₂
    linarith
  nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a - c : ℤ), sq_nonneg (b - c : ℤ),
    sq_pos_of_ne_zero (show (a - b : ℤ) ≠ 0 by
      intro h4
      apply h₀
      linarith
    ), sq_pos_of_ne_zero (show (a - c : ℤ) ≠ 0 by
      intro h5
      apply h₁
      linarith
    ), sq_pos_of_ne_zero (show (b - c : ℤ) ≠ 0 by
      intro h6
      apply h₂
      linarith
    ), sq_nonneg (a + b + c : ℤ), sq_nonneg (a - b + 1 : ℤ), sq_nonneg (a - c + 1 : ℤ), sq_nonneg (b - c + 1 : ℤ)]