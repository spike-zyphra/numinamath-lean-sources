import Mathlib

theorem number_theory_114504 (n : ℕ) :
    ¬∃ k, n^2 + 7 * n + 8 = k * (k + 1) := by 
  rintro ⟨k, hk⟩
  have eq1 : 4 * (n ^ 2 + 7 * n + 8) = 4 * (k * (k + 1)) := by 
    rw [hk]
  have eq2 : (2 * n + 7 : ℤ)^2 = (2 * k + 1 : ℤ)^2 + 16 := by
    have eq3 : (4 * (n ^ 2 + 7 * n + 8) : ℤ) = (4 * (k * (k + 1)) : ℤ) := by
      exact_mod_cast eq1
    nlinarith 
  -- From $(2n + 7)^2 = (2k + 1)^2 + 16$ we get a contradiction
  have eq3 : (2 * n + 7 + (2 * k + 1) : ℤ) * (2 * n + 7 - (2 * k + 1) : ℤ) = 16 := by 
    linarith [eq2]
  have eq4 : (2 * n + 7 + (2 * k + 1) : ℤ) ∣ 16 := by 
    use (2 * n + 7 - (2 * k + 1) : ℤ)
    linarith 
  have eq5 : (2 * n + 7 + (2 * k + 1) : ℤ) ≤ 16 := by 
    apply Int.le_of_dvd (by norm_num) eq4
  have eq6 : (2 * n + 7 + (2 * k + 1) : ℤ) ≥ -16 := by 
    have eq7 : -(2 * n + 7 + (2 * k + 1) : ℤ) ∣ 16 := by 
      exact Int.neg_dvd.2 eq4
    have eq8 : -(2 * n + 7 + (2 * k + 1) : ℤ) ≤ 16 := by 
      apply Int.le_of_dvd (by norm_num) eq7
    omega 
  interval_cases h : (2 * n + 7 + (2 * k + 1) : ℤ) <;> omega