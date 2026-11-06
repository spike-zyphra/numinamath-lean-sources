import Mathlib

theorem number_theory_328343 (n : ℕ) (d : ℕ) (hd : d > 1) (h1 : d ∣ 11 * n + 10) (h2 : d ∣ 10 * n + 3) :
    d = 67 := by 
  have h3 : d ∣ 67 := by 
    have h4 : d ∣ 10 * (11 * n + 10) := by 
      exact dvd_mul_of_dvd_right h1 10 
    have h5 : d ∣ 11 * (10 * n + 3) := by 
      exact dvd_mul_of_dvd_right h2 11 
    have h6 : 67 = 10 * (11 * n + 10) - 11 * (10 * n + 3) := by 
      omega 
    rw [h6] 
    exact Nat.dvd_sub' h4 h5 
  have h4 : d ≤ 67 := by 
    exact Nat.le_of_dvd (show 0 < 67 by norm_num) h3 
  have h5 : d ≥ 67 := by 
    by_contra h 
    push_neg at h 
    have h6 : d ∣ 67 := h3 
    have h7 : d ≤ 67 := by 
      exact Nat.le_of_dvd (show 0 < 67 by norm_num) h3 
    interval_cases d <;> norm_num at h1 h2 h6 <;> omega 
  have h6 : d = 67 := by 
    linarith 
  exact h6