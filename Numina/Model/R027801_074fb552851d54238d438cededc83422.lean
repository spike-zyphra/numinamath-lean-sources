import Mathlib

theorem algebra_263041 : IsLeast {n : ℤ | ∃ x y : ℕ, n = 3 * x ^ 2 - 12 * x * y + y ^ 4} (-32) := by 
  constructor
  · -- Show -32 is in the set
    use 4, 2
    all_goals norm_num
  · -- Show -32 is the smallest
    intro n hn
    rcases hn with ⟨x, y, rfl⟩
    have h1 : (3 * x ^ 2 : ℤ) - 12 * x * y + y ^ 4 ≥ -32 := by
      have h2 : y ≥ 0 := by omega
      have h3 : (y : ℤ) ≥ 0 := by exact_mod_cast show (0 : ℕ) ≤ y by omega
      have h10 : (3 * (x : ℤ) ^ 2 - 12 * (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 4 : ℤ) ≥ -32 := by
        by_cases h15 : (y : ℤ) ≤ 3
        · -- if y ≤ 3, then y can be 0, 1, 2, 3
          have h100 : (y : ℤ) = 0 ∨ (y : ℤ) = 1 ∨ (y : ℤ) = 2 ∨ (y : ℤ) = 3 := by 
            omega
          rcases h100 with (h | h | h | h)
          · -- y = 0
            rw [show (y : ℤ) = 0 by linarith] 
            nlinarith [sq_nonneg ((x : ℤ) : ℤ)]
          · -- y = 1
            rw [show (y : ℤ) = 1 by linarith] 
            nlinarith [sq_nonneg ((x : ℤ) - 2 : ℤ), sq_nonneg ((x : ℤ) : ℤ)]
          · -- y = 2
            rw [show (y : ℤ) = 2 by linarith] 
            nlinarith [sq_nonneg ((x : ℤ) - 4 : ℤ), sq_nonneg ((x : ℤ) : ℤ)]
          · -- y = 3
            rw [show (y : ℤ) = 3 by linarith] 
            nlinarith [sq_nonneg ((x : ℤ) - 6 : ℤ), sq_nonneg ((x : ℤ) : ℤ)]
        · -- if y > 3
          have h16 : (y : ℤ) > 3 := by omega
          have h17 : (y : ℤ) ≥ 4 := by omega
          nlinarith [sq_nonneg ((x : ℤ) - 2 * (y : ℤ) : ℤ), sq_nonneg ((y : ℤ) ^ 2 - 12 : ℤ), sq_nonneg ((y : ℤ) : ℤ), sq_nonneg ((y : ℤ) - 4 : ℤ), sq_nonneg ((y : ℤ) ^ 2 - 16 : ℤ), sq_nonneg ((y : ℤ) ^ 2 - 12 : ℤ), mul_nonneg (show 0 ≤ (y : ℤ) by nlinarith) (show 0 ≤ (y : ℤ) by nlinarith)]
      linarith
    linarith