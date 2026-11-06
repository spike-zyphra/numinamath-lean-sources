import Mathlib

theorem number_theory_113326 (a b c : ℤ) (h₀ : a * b * c = 32) (h₁ : a + b + c = 3) :
    min (min a b) c = -4 := by
  have h2 : a ∣ 32 := by
    use b * c
    all_goals linarith
  have h3 : a ≤ 32 := by
    apply Int.le_of_dvd (by norm_num) h2
  have h4 : a ≥ -32 := by
    have h5 : a ∣ 32 := by
      use b * c
      all_goals linarith
    have h6 : -a ∣ 32 := by
      exact Int.neg_dvd.2 h5
    have h7 : -a ≤ 32 := by
      apply Int.le_of_dvd (by norm_num) h6
    omega
  have h8 : b ∣ 32 := by
    use a * c
    all_goals linarith
  have h9 : b ≤ 32 := by
    apply Int.le_of_dvd (by norm_num) h8
  have h10 : b ≥ -32 := by
    have h11 : b ∣ 32 := by
      use a * c
      all_goals linarith
    have h12 : -b ∣ 32 := by
      exact Int.neg_dvd.2 h11
    have h13 : -b ≤ 32 := by
      apply Int.le_of_dvd (by norm_num) h12
    omega
  have h14 : c ∣ 32 := by
    use a * b
    all_goals linarith
  have h15 : c ≤ 32 := by
    apply Int.le_of_dvd (by norm_num) h14
  have h16 : c ≥ -32 := by
    have h17 : c ∣ 32 := by
      use a * b
      all_goals linarith
    have h18 : -c ∣ 32 := by
      exact Int.neg_dvd.2 h17
    have h19 : -c ≤ 32 := by
      apply Int.le_of_dvd (by norm_num) h18
    omega
  have h17 : c = 3 - a - b := by
    linarith
  rw [h17] at h₀
  have h18 : a * b * (3 - a - b) = 32 := h₀
  interval_cases a <;> try { omega } <;> interval_cases b <;> omega