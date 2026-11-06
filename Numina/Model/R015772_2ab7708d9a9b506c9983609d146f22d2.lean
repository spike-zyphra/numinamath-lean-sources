import Mathlib

theorem number_theory_66681 (k : ℤ) :
    IsSquare (k + 1) ∧ IsSquare (16 * k + 1) ↔ k = 0 ∨ k = 3 := by 
  constructor
  · -- Assume IsSquare (k + 1) ∧ IsSquare (16 * k + 1)
    rintro ⟨h1, h2⟩ 
    rcases h1 with ⟨a, ha⟩
    rcases h2 with ⟨b, hb⟩
    -- Now we have k + 1 = a^2 and 16k + 1 = b^2.
    -- So we get 16(a^2 - 1) + 1 = b^2, which is 16a^2 - 15 = b^2.
    -- This can be written as (4a) ^ 2 - b^2 = 15, or (4a - b)(4a + b) = 15.
    have h_eq : (4 * a - b) * (4 * a + b) = 15 := by 
      nlinarith [ha, hb]
    have h7 : (4 * a - b) ∣ 15 := by
      use (4 * a + b)
      all_goals nlinarith 
    have h8 : (4 * a - b) ≤ 15 := by 
      exact Int.le_of_dvd (by norm_num) h7
    have h9 : (4 * a - b) ≥ -15 := by 
      have h10 : (- (4 * a - b) ) ∣ 15 := by 
        exact Int.neg_dvd.2 h7
      have h11 : (- (4 * a - b) ) ≤ 15 := by 
        apply Int.le_of_dvd (by norm_num) h10
      omega
    -- Now we can apply exhaustive search to the bounded integer factors
    interval_cases h10 : (4 * a - b) <;> try { 
      omega
    }
    <;> try { 
      -- Now the unsolved goals can't happen
      have : a ≤ 3 := by
        nlinarith [sq_nonneg (b), sq_nonneg (a), sq_nonneg (4 * a - b), sq_nonneg (4 * a + b)]
      have : a ≥ -3 := by
        nlinarith [sq_nonneg (b), sq_nonneg (a), sq_nonneg (4 * a - b), sq_nonneg (4 * a + b)]
      interval_cases a <;> try { 
        omega
      }
    }
  · -- Assume k = 0 or k = 3, prove both are squares
    rintro (h | h)
    · -- k = 0
      rw [h]
      constructor
      · -- Show 0 + 1 is a square
        exact ⟨1, by norm_num⟩
      · -- Show 16 * 0 + 1 is a square
        exact ⟨1, by norm_num⟩
    · -- k = 3
      rw [h]
      constructor
      · -- Show 3 + 1 is a square
        exact ⟨2, by norm_num⟩
      · -- Show 16 * 3 + 1 is a square
        exact ⟨7, by norm_num⟩