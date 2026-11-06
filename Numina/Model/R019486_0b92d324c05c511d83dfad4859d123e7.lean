import Mathlib

theorem algebra_303460 (a b c : ℤ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c) :
    4 * (a^2 + b^2 + c^2) - (a + b + c)^2 ≥ 8 := by
  have h3 : (a - b) ^ 2 > 0 := by 
    have h4 : a - b ≠ 0 := by
      intro h
      apply h₀
      linarith
    have h5 : (a - b) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h4
    linarith
  have h4 : (b - c) ^ 2 > 0 := by 
    have h5 : b - c ≠ 0 := by
      intro h
      apply h₂
      linarith
    have h6 : (b - c) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h5
    linarith
  have h5 : (a - c) ^ 2 > 0 := by 
    have h6 : a - c ≠ 0 := by
      intro h
      apply h₁
      linarith
    have h7 : (a - c) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h6
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
            sq_pos_of_ne_zero (show (a - b : ℤ) ≠ 0 by
              intro h
              apply h₀
              linarith
            ), sq_pos_of_ne_zero (show (b - c : ℤ) ≠ 0 by
              intro h
              apply h₂
              linarith
            ), sq_pos_of_ne_zero (show (a - c : ℤ) ≠ 0 by
              intro h
              apply h₁
              linarith
            )
          ]