import Mathlib

theorem number_theory_180759 (m n : ℕ) (h₀ : ¬ 3 ∣ m) : 3 ∣ n^3 - m^2 * n := by 
  have h1 : n ^ 3 % 3 = n % 3 := by
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h2 with (h | h | h)
    · 
      simp [h, pow_succ, Nat.mul_mod, Nat.add_mod]
    · 
      simp [h, pow_succ, Nat.mul_mod, Nat.add_mod]
    · 
      simp [h, pow_succ, Nat.mul_mod, Nat.add_mod]
  have h_m2_mod_3 : m ^ 2 % 3 = 1 := by
    have h_m_mod_3 : m % 3 = 1 ∨ m % 3 = 2 := by 
      have h3 : ¬ (3 ∣ m) := h₀
      have h4 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by 
        omega
      rcases h4 with (h | h | h)
      · 
        have h5 : 3 ∣ m := by 
          omega
        contradiction
      · 
        tauto
      · 
        tauto
    rcases h_m_mod_3 with (h | h)
    · 
      simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
    · 
      simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
  have h3 : (m ^ 2 * n) % 3 = n % 3 := by
    have h4 : m ^ 2 % 3 = 1 := h_m2_mod_3 
    simp [Nat.mul_mod, h4, Nat.mul_mod]
  have h4 : (n ^ 3 - m ^ 2 * n) % 3 = 0 := by
    have h5 : n ^ 3 % 3 = n % 3 := h1
    have h6 : (m ^ 2 * n) % 3 = n % 3 := h3 
    omega
  exact Nat.dvd_of_mod_eq_zero h4