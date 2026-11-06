import Mathlib

theorem number_theory_112223 (x : ℤ) :
    ∃ n, n^2 = x^4 + x^3 + x^2 + x + 1 ↔ x = -1 ∨ x = 0 ∨ x = 3 := by
  by_cases h1 : x = -1
  · -- Assume x = -1 
    use 1 
    simp [h1] 
  · -- Assume x ≠ -1 
    by_cases h2 : x = 0 
    · -- Assume x = 0 
      use 1 
      simp [h2] 
    · -- Assume x ≠ -1, 0 
      by_cases h3 : x = 3 
      · -- Assume x = 3 
        use 11 
        simp [h3] 
        <;> nlinarith 
      · -- Assume x ≠ -1, 0, 3 
        have h4 : x^4 + x^3 + x^2 + x + 1 > 0 := by 
          nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x + 2)]
        use 0 
        constructor 
        · -- Assume n ^2 = polynomial(x)
          intro h 
          nlinarith 
        · -- Assume the right side 
          rintro (h7 | h8 | h9) 
          · -- Assume x = -1 
            exfalso 
            tauto 
          · -- Assume x = 0 
            exfalso 
            tauto 
          · -- Assume x = 3 
            exfalso 
            tauto