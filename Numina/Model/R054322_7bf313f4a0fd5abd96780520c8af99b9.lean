import Mathlib

theorem number_theory_177567 (n : ℕ) :
    3 ∣ (n^3 + (n+1)^3 + (n+2)^3) := by
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h | h | h)
  · -- Case where n % 3 = 0
    have h11 : n % 3 = 0 := h
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 3 = 0 := by
      have h3 : n^3 % 3 = 0 := by
        simp [Nat.pow_mod, h11]
      have h4 : (n + 1)^3 % 3 = 1 := by
        have h5 : (n + 1) % 3 = 1 := by 
          omega
        simp [Nat.pow_mod, h5]
      have h6 : (n + 2)^3 % 3 = 2 := by
        have h7 : (n + 2) % 3 = 2 := by 
          omega
        simp [Nat.pow_mod, h7]
      omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n % 3 = 1
    have h11 : n % 3 = 1 := h
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 3 = 0 := by
      have h3 : n^3 % 3 = 1 := by
        simp [Nat.pow_mod, h11]
      have h4 : (n + 1)^3 % 3 = 2 := by
        have h5 : (n + 1) % 3 = 2 := by 
          omega
        simp [Nat.pow_mod, h5]
      have h6 : (n + 2)^3 % 3 = 0 := by
        have h7 : (n + 2) % 3 = 0 := by 
          omega
        simp [Nat.pow_mod, h7]
      omega
    exact Nat.dvd_of_mod_eq_zero h2
  · -- Case where n % 3 = 2
    have h11 : n % 3 = 2 := h
    have h2 : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 3 = 0 := by
      have h3 : n^3 % 3 = 2 := by
        simp [Nat.pow_mod, h11]
      have h4 : (n + 1)^3 % 3 = 0 := by
        have h5 : (n + 1) % 3 = 0 := by 
          omega
        simp [Nat.pow_mod, h5]
      have h6 : (n + 2)^3 % 3 = 1 := by
        have h7 : (n + 2) % 3 = 1 := by 
          omega
        simp [Nat.pow_mod, h7]
      omega
    exact Nat.dvd_of_mod_eq_zero h2