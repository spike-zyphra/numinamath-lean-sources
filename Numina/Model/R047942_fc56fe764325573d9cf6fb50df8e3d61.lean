import Mathlib

theorem number_theory_51121 (a b : ℤ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : a^2 - b^4 = 2009) : a + b = 47 := by
  have h2 : a^2 = b^4 + 2009 := by
    linarith
  have h4 : (a - b^2) * (a + b^2) = 2009 := by
    nlinarith
  have h5 : a - b^2 ∣ 2009 := by
    use a + b^2
    all_goals nlinarith
  have h6 : a - b^2 ≥ 1 := by
    have h7 : a - b^2 > 0 := by
      nlinarith [sq_nonneg (a - b^2), sq_nonneg (a + b^2)]
    omega
  have h7 : a - b^2 ≤ 2009 := by
    exact Int.le_of_dvd (by norm_num) h5
  interval_cases h8 : a - b^2 <;> norm_num at h5 h4 <;> try { 
    all_goals
      have hb2 : b ≤ 32 := by
        nlinarith [sq_nonneg (a - 45), sq_nonneg (b^2 - 4)]
      have hb3 : b ≤ 32 := by
        nlinarith
      have hb4 : b < 33 := by
        nlinarith
      interval_cases b <;> norm_num at h4 h2 <;> omega
  }
  <;> omega