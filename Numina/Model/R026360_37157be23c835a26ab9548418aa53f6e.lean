import Mathlib

theorem algebra_299409 (n : ℤ) (h : ∃ a b : ℤ, a^2 - 6*a - 4*n^2 - 32*n = 0 ∧ b^2 - 6*b - 4*n^2 - 32*n = 0) :
    n = -18 ∨ n = -8 ∨ n = 0 ∨ n = 10 := by
  rcases h with ⟨a, b, ha, hb⟩
  have h_sub : (a - b) * (a + b - 6) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.1 h_sub) with h1 h2
  · -- Case where a - b = 0, so a = b
    have h1' : a = b := by linarith
    rw [show b = a by linarith [h1']] at hb
    have h_eq : (a - 3) ^ 2 = 4 * (n + 4) ^ 2 - 55 := by 
      nlinarith 
    have h2 : (a - 2 * n - 11) * (a + 2 * n + 5) = -55 := by 
      nlinarith 
    have h3 : (a - 2 * n - 11) ∣ (-55 : ℤ) := by 
      use (a + 2 * n + 5)
      linarith
    have h4 : (a - 2 * n - 11) ∣ (55 : ℤ) := by 
      exact Int.dvd_neg.mp h3
    have h5 : (a - 2 * n - 11) ≤ 55 := by 
      apply Int.le_of_dvd (by norm_num) h4
    have h6 : (a - 2 * n - 11) ≥ -55 := by
      have h7 : (- (a - 2 * n - 11) ) ∣ (55 : ℤ) := by 
        exact Int.neg_dvd.2 h4
      have h8 : - (a - 2 * n - 11) ≤ 55 := by 
        apply Int.le_of_dvd (by norm_num) h7
      omega
    interval_cases h : (a - 2 * n - 11) <;> omega
  · -- Case where a + b - 6 = 0, so a + b = 6
    have h2' : a + b = 6 := by linarith
    have h_eq2 : b = 6 - a := by linarith 
    rw [h_eq2] at hb 
    -- Now both equations give the same constraint
    have h_eq : (a - 3) ^ 2 = 4 * (n + 4) ^ 2 - 55 := by 
      nlinarith 
    have h2 : (a - 2 * n - 11) * (a + 2 * n + 5) = -55 := by 
      nlinarith 
    have h3 : (a - 2 * n - 11) ∣ (-55 : ℤ) := by 
      use (a + 2 * n + 5)
      linarith
    have h4 : (a - 2 * n - 11) ∣ (55 : ℤ) := by 
      exact Int.dvd_neg.mp h3
    have h5 : (a - 2 * n - 11) ≤ 55 := by 
      apply Int.le_of_dvd (by norm_num) h4
    have h6 : (a - 2 * n - 11) ≥ -55 := by 
      have h7 : (- (a - 2 * n - 11) ) ∣ (55 : ℤ) := by 
        exact Int.neg_dvd.2 h4
      have h8 : - (a - 2 * n - 11) ≤ 55 := by 
        apply Int.le_of_dvd (by norm_num) h7
      omega
    interval_cases h : (a - 2 * n - 11) <;> omega