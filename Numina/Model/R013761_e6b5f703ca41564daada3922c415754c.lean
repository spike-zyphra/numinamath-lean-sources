import Mathlib

theorem number_theory_47710 :
    IsGreatest {k | ∀ n : ℕ, n > 0 → n % 10 = 4 → k ∣ n * (n + 1) * (n + 2)} 120 := by 
  constructor
  · -- Show 120 is in the set
    show ∀ n : ℕ, n > 0 → n % 10 = 4 → 120 ∣ n * (n + 1) * (n + 2)
    intro n hn h
    have h1 : n % 2 = 0 := by
      omega
    have h4 : (n * (n + 1) * (n + 2)) % 8 = 0 := by
      have h4 : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4)
      · 
        simp [h4, Nat.mul_mod, Nat.add_mod]
      · 
        simp [h4, Nat.mul_mod, Nat.add_mod]
      · 
        simp [h4, Nat.mul_mod, Nat.add_mod]
      · 
        simp [h4, Nat.mul_mod, Nat.add_mod]
    have h5 : (n * (n + 1) * (n + 2)) % 3 = 0 := by
      have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases h1 with (h1 | h1 | h1)
      · 
        simp [h1, Nat.mul_mod, Nat.add_mod]
      · 
        simp [h1, Nat.mul_mod, Nat.add_mod]
      · 
        simp [h1, Nat.mul_mod, Nat.add_mod]
    have h6 : (n * (n + 1) * (n + 2)) % 5 = 0 := by
      have h4 : n % 5 = 4 := by
        omega
      simp [h4, Nat.mul_mod, Nat.add_mod]
    omega
  · -- Show 120 is greatest
    intro k hk
    have h1 : ∀ n : ℕ, n > 0 → n % 10 = 4 → k ∣ n * (n + 1) * (n + 2) := hk
    have h2 := h1 4 (by norm_num) (by norm_num)
    have h3 : k ∣ 120 := h2
    have h4 : k ≤ 120 := by
      exact Nat.le_of_dvd (by norm_num) h3
    linarith