import Mathlib

theorem algebra_311273 (k : ℤ) :
    ∃ x : ℤ, k * x ^ 2 - 2 * (3 * k - 1) * x + 9 * k - 1 = 0 ↔ k = -3 ∨ k = -7 := by
  by_cases h1 : k = -3
  · -- Assume k = -3, prove ∃ x : ℤ, k * x ^ 2 - 2 * (3 * k - 1) * x + 9 * k - 1 = 0 ↔ k = -3 ∨ k = -7 
    use 2 
    rw [h1] 
    norm_num 
  · -- Assume k ≠ -3 
    by_cases h2 : k = -7 
    · -- Assume k = -7, prove ∃ x : ℤ, k * x ^ 2 - 2 * (3 * k - 1) * x + 9 * k - 1 = 0 ↔ k = -3 ∨ k = -7 
      use 4 
      rw [h2] 
      norm_num 
    · -- Assume k ≠ -3 and k ≠ -7 
      use 0 
      constructor 
      · -- Assume k * 0 ^ 2 - 2 * (3 * k - 1) * 0 + 9 * k - 1 = 0, prove k = -3 ∨ k = -7 
        intro h 
        have h3 : 9 * k - 1 = 0 := by 
          nlinarith 
        omega 
      · -- Assume k = -3 ∨ k = -7, prove k * 0 ^ 2 - 2 * (3 * k - 1) * 0 + 9 * k - 1 = 0 
        intro h 
        cases h with 
        | inl h1 => 
          exfalso 
          contradiction 
        | inr h2 => 
          exfalso 
          contradiction