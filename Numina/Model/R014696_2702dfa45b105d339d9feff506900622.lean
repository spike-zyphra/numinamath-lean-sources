import Mathlib

theorem number_theory_258533 (a : ℕ) :
    ∃ n, n^2 = a^2 + a + 1589 ↔ a = 1588 ∨ a = 28 ∨ a = 316 ∨ a = 43 := by 
  by_cases h1588 : a = 1588
  · -- Case a = 1588.
    use 1589
    simp [h1588]
  · -- Case a ≠ 1588.
    by_cases h28 : a = 28
    · -- Case a = 28.
      use 49
      simp [h28]
    · -- Case a ≠ 1588 and a ≠ 28.
      by_cases h316 : a = 316
      · -- Case a = 316.
        use 319
        simp [h316]
        <;> omega
      · -- Case a ≠ 1588, a ≠ 28, a ≠ 316.
        by_cases h43 : a = 43
        · -- Case a = 43.
          use 59
          simp [h43]
        · -- Case a ≠ 1588, a ≠ 28, a ≠ 316, a ≠ 43.
          use 0
          have h1588' : a ≠ 1588 := by omega
          have h28' : a ≠ 28 := by omega
          have h316' : a ≠ 316 := by omega
          have h43' : a ≠ 43 := by omega
          constructor
          · -- Forward direction: if 0 = a^2 + a + 1589 then the disjunction is true.
            intro h
            have h1 : a ^ 2 + a + 1589 = 0 := by omega
            nlinarith
          · -- Backward direction: if the disjunction is true, then 0 = a^2 + a + 1589.
            intro h
            rcases h with (r | r | r | r)
            · -- Case a = 1588.
              exfalso
              omega
            · -- Case a = 28.
              exfalso
              omega
            · -- Case a = 316.
              exfalso
              omega
            · -- Case a = 43.
              exfalso
              omega