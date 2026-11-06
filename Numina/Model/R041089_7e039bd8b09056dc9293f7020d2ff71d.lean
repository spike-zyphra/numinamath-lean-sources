import Mathlib

theorem algebra_166104 (a b : ℤ) (_ : 0 < a) (h₀ : 0 < b) :
    a^3 + (a + b)^2 + b ≠ b^3 + a + 2 := by
  rintro heq
  have h2 : b < a + 2 := by
    nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b + 1 : ℤ), 
        sq_pos_of_pos (show (0 : ℤ) < a from by linarith), 
        sq_pos_of_pos (show (0 : ℤ) < b from by linarith), 
        mul_pos (show (0 : ℤ) < a from by linarith) (show (0 : ℤ) < b from by linarith)
      ]
  have h3 : a < b + 2 := by 
    nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b + 1 : ℤ), 
        sq_pos_of_pos (show (0 : ℤ) < a from by linarith), 
        sq_pos_of_pos (show (0 : ℤ) < b from by linarith), 
        mul_pos (show (0 : ℤ) < a from by linarith) (show (0 : ℤ) < b from by linarith)
      ]
  have h4 : b ≤ a + 1 := by 
    omega
  have h5 : a ≤ b + 1 := by 
    omega
  have h10 : a - b = 0 ∨ a - b = 1 ∨ a - b = -1 := by 
    have h3 : a - b ≤ 1 := by 
      omega
    have h4 : a - b ≥ -1 := by 
      omega
    omega
  rcases h10 with h10 | h10 | h10
  · -- Case a - b = 0, so a = b
    have h11 : b = a := by linarith 
    rw [show b = a by linarith] at heq 
    nlinarith [sq_nonneg (a^2 : ℤ), sq_pos_of_pos (show 0 < (a : ℤ) by linarith)]
  · -- Case a - b = 1, so b = a - 1 
    have h12 : b = a - 1 := by linarith 
    rw [h12] at heq 
    nlinarith [sq_nonneg (a : ℤ), sq_nonneg (a : ℤ), sq_nonneg (a - 1 : ℤ), sq_nonneg (a + 1 : ℤ)]
  · -- Case a - b = -1, so a = b - 1 
    have h13 : a = b - 1 := by linarith 
    rw [show a = b - 1 by linarith] at heq 
    nlinarith [sq_nonneg (b : ℤ), sq_nonneg (b : ℤ), sq_nonneg (b - 1 : ℤ), sq_nonneg (b + 1 : ℤ)]