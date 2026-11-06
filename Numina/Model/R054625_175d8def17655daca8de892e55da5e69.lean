import Mathlib

theorem number_theory_275789 (n : ℤ) (h : n > 4) :
    ¬ ∃ m : ℕ, m^2 = n^2 - 3 * n := by
  rintro ⟨m, hm⟩
  have h1 : (n : ℤ)^2 - 3 * (n : ℤ) ≥ 0 := by
    have h2 : (n : ℤ)^2 - 3 * (n : ℤ) = (m : ℤ)^2 := by
      norm_num at hm ⊢
      linarith 
    nlinarith [sq_nonneg (m : ℤ)]
  have h3 : n ≥ 5 := by linarith
  have eq1 : (n : ℤ) ^ 2 - 3 * (n : ℤ) = (m : ℤ) ^ 2 := by
    norm_num at hm ⊢
    linarith
  have eq2 : (2 * (n : ℤ) - 3) ^ 2 - 4 * ((m : ℤ) ^ 2) = 9 := by
    nlinarith [eq1]
  have eq3 : ((2 * (n : ℤ) - 3) - 2 * (m : ℤ)) * ((2 * (n : ℤ) - 3) + 2 * (m : ℤ)) = 9 := by
    nlinarith [eq2]
  have h5 : ((2 * (n : ℤ) - 3) - 2 * (m : ℤ)) ∣ 9 := by 
    use ((2 * (n : ℤ) - 3) + 2 * (m : ℤ))
    linarith [eq3]
  have h6 : ((2 * (n : ℤ) - 3) - 2 * (m : ℤ)) ≤ 9 := by 
    apply Int.le_of_dvd (by norm_num) h5
  have h7 : ((2 * (n : ℤ) - 3) - 2 * (m : ℤ)) ≥ -9 := by 
    have h7 : -((2 * (n : ℤ) - 3) - 2 * (m : ℤ)) ∣ 9 := by 
      exact Int.neg_dvd.2 h5
    have h8 : -((2 * (n : ℤ) - 3) - 2 * (m : ℤ)) ≤ 9 := by 
      apply Int.le_of_dvd (by norm_num) h7
    linarith
  interval_cases k1 : (2 * (n : ℤ) - 3) - 2 * (m : ℤ) <;> 
    omega