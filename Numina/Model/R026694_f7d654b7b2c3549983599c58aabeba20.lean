import Mathlib

theorem number_theory_326861 : ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 4 * a * (a + 1) = b * (b + 3) := by 
  rintro ⟨a, b, ha, hb, heq⟩

  have heq2 : (2 * b + 3 : ℤ) ^ 2 = 4 * (2 * a + 1 : ℤ) ^ 2 + 5 := by
    have h1 : (4 * a * (a + 1) : ℤ) = (b * (b + 3) : ℤ) := by
      exact_mod_cast heq
    nlinarith

  have h1 : (2 * b + 3 : ℤ) ^ 2 - 4 * (2 * a + 1 : ℤ) ^ 2 = 5 := by
    linarith [heq2]

  have h2 : ((2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ)) * ((2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ)) = 5 := by 
    nlinarith

  have h4 : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ)) = 1 ∨ 
            ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ)) = 5 ∨ 
            ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ)) = -1 ∨ 
            ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ)) = -5 := by
    have h5 : ((2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ)) * ((2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ)) = 5 := h2
    have h6 : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) ∣ 5 := by
      use ((2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ))
      all_goals nlinarith
    have h7 : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) ∣ 5 := h6
    have h8 : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) ≤ 5 := by 
      exact Int.le_of_dvd (by norm_num) h7 
    have h9 : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) ≥ -5 := by 
      have h10 : - ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) ∣ 5 := by 
        exact Int.neg_dvd.2 h7 
      have h11 : - ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) ≤ 5 := by 
        exact Int.le_of_dvd (by norm_num) h10 
      omega 
    interval_cases ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) <;> 
      omega

  rcases h4 with h4 | h4 | h4 | h4

  · -- When $c1 = 1$, so $Y' = 1$, solve to get $Y=3, X=1$.
    have h5 : (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) = 5 := by
      have h5' : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) * ( (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) ) = 5 := h2
      rw [h4] at h5'
      nlinarith

    have h7 : (2 * b + 3 : ℤ) = 3 := by 
      omega
    have h8 : (2 * a + 1 : ℤ) = 1 := by 
      omega
    have h9 : b = 0 := by
      omega
    omega

  · -- When $c1 = 5$, solve to get $Y=3, X=-1$.
    have h5 : (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) = 1 := by
      have h5' : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) * ( (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) ) = 5 := h2
      rw [h4] at h5'
      nlinarith

    omega

  · -- When $c1 = -1$, solve to get $Y=-3, X=1$.
    have h5 : (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) = -5 := by
      have h5' : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) * ( (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) ) = 5 := h2
      rw [h4] at h5'
      nlinarith

    omega

  · -- When $c1 = -5$, solve to get $Y=-3, X=-1$.
    have h5 : (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) = -1 := by
      have h5' : ( (2 * b + 3 : ℤ) - 2 * (2 * a + 1 : ℤ) ) * ( (2 * b + 3 : ℤ) + 2 * (2 * a + 1 : ℤ) ) = 5 := h2
      rw [h4] at h5'
      nlinarith

    omega