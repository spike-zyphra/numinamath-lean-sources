import Mathlib

theorem number_theory_173984 (p : ℕ) (hp : p.Prime) (h : 3 < p) : 24 ∣ (p - 1) * (p + 1) := by 
  have h1 : p % 2 = 1 := by 
    by_contra h1
    push_neg at h1
    have h2 : p % 2 = 0 := by 
      omega
    have h3 : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    tauto
  have h5 : (p - 1) * (p + 1) % 3 = 0 := by
    have h2' : p % 3 = 1 ∨ p % 3 = 2 := by
      have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
        omega
      by_contra h4
      push_neg at h4
      have h4' : p % 3 = 0 := by
        omega
      have h5 : 3 ∣ p := by
        omega
      have h6 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
      tauto 
    rcases h2' with (h2' | h2')
    · -- case p % 3 = 1
      simp [h2', Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq] 
    · -- case p % 3 = 2
      simp [h2', Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq]
  have h6 : (p - 1) * (p + 1) % 8 = 0 := by
    have h5 : p % 2 = 1 := h1 
    have h6' : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
      omega 
    rcases h6' with (h6' | h6' | h6' | h6')
    · -- Case p % 8 = 1 
      have h7 : p % 8 = 1 := h6'
      have h8 : (p - 1) * (p + 1) % 8 = 0 := by
        have h7 : p % 8 = 1 := h7 
        have h11 : p % 8 = 1 := h7
        have h12 : (p - 1) % 8 = 0 := by
          omega
        have h13 : (p + 1) % 8 = 2 := by
          omega 
        simp [Nat.mul_mod, h12, h13]
      assumption 
    · -- Case p % 8 = 3 
      have h7 : p % 8 = 3 := h6'
      have h8 : (p - 1) * (p + 1) % 8 = 0 := by 
        have h7 : p % 8 = 3 := h7 
        have h12 : (p - 1) % 8 = 2 := by 
          omega 
        have h13 : (p + 1) % 8 = 4 := by 
          omega 
        simp [Nat.mul_mod, h12, h13]
      assumption 
    · -- Case p % 8 = 5 
      have h7 : p % 8 = 5 := h6'
      have h8 : (p - 1) * (p + 1) % 8 = 0 := by
        have h7 : p % 8 = 5 := h7 
        have h12 : (p - 1) % 8 = 4 := by 
          omega 
        have h13 : (p + 1) % 8 = 6 := by 
          omega 
        simp [Nat.mul_mod, h12, h13]
      assumption 
    · -- Case p % 8 = 7 
      have h7 : p % 8 = 7 := h6'
      have h8 : (p - 1) * (p + 1) % 8 = 0 := by 
        have h7 : p % 8 = 7 := h7 
        have h12 : (p - 1) % 8 = 6 := by 
          omega 
        have h13 : (p + 1) % 8 = 0 := by 
          omega 
        simp [Nat.mul_mod, h12, h13]
      assumption
  omega