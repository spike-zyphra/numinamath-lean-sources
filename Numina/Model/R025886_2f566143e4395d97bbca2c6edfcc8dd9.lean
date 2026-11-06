import Mathlib

theorem number_theory_159951 (M : ℕ) (hM : M ≠ 1) (hM1 : ∀ n, n % M = (Nat.digits 10 n).sum % M) :
    M = 3 ∨ M = 9 := by
  have h1 := hM1 10
  have h2 : 10 % M = 1 % M := by
    simp [Nat.digits, Nat.digitsAux] at h1 ⊢
    omega
  have h3 : M ∣ 9 := by
    have h4 : (10 : ℕ) % M = 1 % M := h2
    have h5 : M ∣ (10 - 1 : ℕ) := by
      have h6 : (10 : ℕ) % M = (1 : ℕ) % M := by 
        simpa using h4
      have h7 : M ∣ (10 - 1 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h6)
      exact h7
    have : (10 - 1 : ℕ) = 9 := by omega
    rw [this] at h5
    exact h5
  have h4 : M = 3 ∨ M = 9 := by 
    have h5 : M ∣ 9 := h3
    have h6 : M ≤ 9 := by
      exact Nat.le_of_dvd (by norm_num) h5
    interval_cases M <;> tauto
  exact h4