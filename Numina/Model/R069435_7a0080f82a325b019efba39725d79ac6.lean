import Mathlib

theorem number_theory_6986 (m : ℤ) (h : m - 1 ∣ m + 1) :
    m - 1 = 1 ∨ m - 1 = -1 ∨ m - 1 = 2 ∨ m - 1 = -2 := by 
  have h1 : m - 1 ∣ 2 := by
    have h2 : m - 1 ∣ m + 1 := h
    have h3 : m - 1 ∣ (m + 1 - (m - 1 : ℤ)) := by 
      apply Int.dvd_sub
      · exact h2
      · exact Int.dvd_refl (m - 1)
    have h4 : m + 1 - (m - 1 : ℤ) = 2 := by 
      ring
    rw [h4] at h3
    exact h3
  have h5 : m - 1 ≤ 2 := by 
    apply Int.le_of_dvd (by norm_num) h1
  have h6 : m - 1 ≥ -2 := by 
    have h7 : -(m - 1) ∣ 2 := by 
      exact Int.neg_dvd.2 h1
    have h8 : -(m - 1) ≤ 2 := by 
      apply Int.le_of_dvd (by norm_num) h7
    linarith 
  interval_cases h8 : m - 1 <;> norm_num at h1 ⊢ <;> tauto