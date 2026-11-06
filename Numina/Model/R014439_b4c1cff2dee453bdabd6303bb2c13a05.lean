import Mathlib

theorem number_theory_156266 {M : ℕ} (hM : M ≠ 1) (h : ∀ n, n % M = (Nat.digits 10 n).sum % M) :
    M = 3 ∨ M = 9 := by 
  have h2 : M ∣ 9 := by 
    have h10 := h 10 
    have h3 : (Nat.digits 10 (10 : ℕ)).sum = 1 := by 
      norm_num 
    rw [h3] at h10 
    have h4 : (10 : ℕ) % M = (1 : ℕ) % M := by 
      omega 
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h4) 
  have h4 : M ∣ 9 := h2
  have h6 : M ≤ 9 := by 
    exact Nat.le_of_dvd (by norm_num) h4 
  have h7 : M = 3 ∨ M = 9 := by 
    interval_cases M <;> norm_num at h4 hM ⊢ 
    <;> omega 
  assumption