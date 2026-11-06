import Mathlib

theorem algebra_244309 (k : ℤ) :
    ∃ x : ℤ, x ^ 2014 + k * x ^ 2 + 36 = 0 ↔
    k = -37 ∨ k = -4 ^ 1006 - 9 ∨ k = -9 ^ 1006 - 4 ∨ k = -36 ^ 1006 - 1 := by 
  by_cases h1 : k = -37 
  · -- Assume k = -37 
    use 1 
    simp [h1] 
  · -- Assume k is not -37 
    by_cases h2 : k = -4 ^ 1006 - 9 
    · -- Assume k = -4 ^ 1006 - 9 
      use 2 
      simp [h2] 
      <;> ring_nf 
    · -- Assume k is not -4 ^ 1006 - 9 
      by_cases h3 : k = -9 ^ 1006 - 4 
      · -- Assume k = -9 ^ 1006 - 4 
        use 3 
        simp [h3] 
        <;> ring_nf 
      · -- Assume k is not -9 ^ 1006 - 4 
        by_cases h4 : k = -36 ^ 1006 - 1 
        · -- Assume k = -36 ^ 1006 - 1 
          use 6 
          simp [h4] 
          <;> ring_nf 
        · -- Assume k does not equal any of the four values. Contradicts? 
          use 0 
          simp at *
          all_goals 
            omega