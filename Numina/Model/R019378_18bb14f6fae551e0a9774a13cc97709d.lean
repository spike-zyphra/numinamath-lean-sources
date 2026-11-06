import Mathlib

theorem number_theory_113389 (a b c : ℤ) (h₀ : a * b * c = 36) (h₁ : a + b + c = 4) :
    min (min a b) c = -4 := by 
  have h2 : a ∣ 36 := by 
    use b * c 
    all_goals 
      nlinarith
  have h3 : b ∣ 36 := by 
    use a * c 
    all_goals 
      nlinarith
  have h4 : c ∣ 36 := by 
    use a * b 
    all_goals 
      nlinarith
  have h5 : a ≤ 36 := by 
    apply Int.le_of_dvd (by norm_num) h2 
  have h6 : a ≥ -36 := by 
    have h7 : -a ∣ 36 := by 
      exact Int.neg_dvd.2 h2 
    have h8 : -a ≤ 36 := by 
      apply Int.le_of_dvd (by norm_num) h7 
    linarith 
  have h7 : b ≤ 36 := by 
    apply Int.le_of_dvd (by norm_num) h3 
  have h8 : b ≥ -36 := by 
    have h9 : -b ∣ 36 := by 
      exact Int.neg_dvd.2 h3 
    have h10 : -b ≤ 36 := by 
      apply Int.le_of_dvd (by norm_num) h9 
    linarith 
  interval_cases a <;> try { 
    omega 
  } 
  <;> try { 
    interval_cases b <;> omega 
  }