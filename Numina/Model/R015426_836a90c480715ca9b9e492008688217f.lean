import Mathlib

theorem number_theory_178845 (M : ℤ) (h : ∃ x, x^2 = M^2 + M + 7) :
    M = -7 ∨ M = -2 ∨ M = 1 ∨ M = 6 := by
  rcases h with ⟨x, hx⟩
  have h1 : (2 * x - (2 * M + 1)) * (2 * x + (2 * M + 1)) = 27 := by 
    nlinarith [hx]
  have h2 : (2 * x - (2 * M + 1)) ∣ 27 := by 
    use (2 * x + (2 * M + 1))
    all_goals linarith
  have h3 : (2 * x - (2 * M + 1)) ≤ 27 := by
    apply Int.le_of_dvd (show 0 < (27 : ℤ) by norm_num) h2
  have h4 : (2 * x - (2 * M + 1)) ≥ -27 := by
    have : (- (2 * x - (2 * M + 1))) ∣ 27 := by
      exact Int.neg_dvd.2 h2
    have : - (2 * x - (2 * M + 1)) ≤ 27 := by 
      apply Int.le_of_dvd (show 0 < (27 : ℤ) by norm_num) this
    linarith
  interval_cases h5 : (2 * x - (2 * M + 1)) <;> omega