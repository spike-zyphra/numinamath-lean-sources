import Mathlib

theorem number_theory_8931 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : ¬ 4 * a * (a + 1) = b * (b + 3) := by
  intro h
  have h1 : 4 * a * (a + 1) = b * (b + 3) := by
    linarith
  have h2 : (2 * b + 3 : ℤ) ^ 2 - 4 * (2 * a + 1 : ℤ) ^ 2 = 5 := by
    nlinarith [h1]
  have h3 : (2 * b + 3 - 2 * (2 * a + 1)) * (2 * b + 3 + 2 * (2 * a + 1)) = 5 := by
    ring_nf at h2 ⊢
    nlinarith
  have h4 : (2 * b + 3 - 2 * (2 * a + 1)) ∣ 5 := by
    use (2 * b + 3 + 2 * (2 * a + 1))
    all_goals linarith [h3]
  have h5 : (2 * b + 3 - 2 * (2 * a + 1)) ≤ 5 := by
    exact Int.le_of_dvd (by norm_num) h4
  have h6 : (2 * b + 3 - 2 * (2 * a + 1)) ≥ -5 := by
    have h7 : (- (2 * b + 3 - 2 * (2 * a + 1)) ) ∣ 5 := by
      exact Int.neg_dvd.2 h4
    have h8 : - (2 * b + 3 - 2 * (2 * a + 1)) ≤ 5 := by
      exact Int.le_of_dvd (by norm_num) h7
    omega
  interval_cases h7 : (2 * b + 3 - 2 * (2 * a + 1)) <;> omega -- use omega to solve the inequalities