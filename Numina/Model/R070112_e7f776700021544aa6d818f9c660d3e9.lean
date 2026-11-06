import Mathlib

theorem number_theory_258691 (n : ℕ) (h₀ : Odd n) (h₁ : 0 < n)
    (h₂ : ¬ 3 ∣ n) : 24 ∣ (n ^ 2 - 1) := by 
  have h8 : (n ^ 2 - 1) % 8 = 0 := by
    have h : n % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h₀
      omega
    have h3 : (n % 8) = 1 ∨ (n % 8) = 3 ∨ (n % 8) = 5 ∨ (n % 8) = 7 := by 
      omega
    rcases h3 with (h | h | h | h)
    · -- case n % 8 = 1
      have h3 : (n ^ 2) % 8 = 1 := by
        have h4 : n % 8 = 1 := h
        norm_num [Nat.pow_mod, h4] at *
      have h4 : (n ^ 2 - 1) % 8 = 0 := by
        omega
      omega
    · -- case n % 8 = 3
      have h3 : (n ^ 2) % 8 = 1 := by
        have h4 : n % 8 = 3 := h
        norm_num [Nat.pow_mod, h4] at *
      have h4 : (n ^ 2 - 1) % 8 = 0 := by
        omega
      omega
    · -- case n % 8 = 5
      have h3 : (n ^ 2) % 8 = 1 := by
        have h4 : n % 8 = 5 := h
        norm_num [Nat.pow_mod, h4] at *
      have h4 : (n ^ 2 - 1) % 8 = 0 := by
        omega
      omega
    · -- case n % 8 = 7
      have h3 : (n ^ 2) % 8 = 1 := by
        have h4 : n % 8 = 7 := h
        norm_num [Nat.pow_mod, h4] at *
      have h4 : (n ^ 2 - 1) % 8 = 0 := by
        omega
      omega
  have h3 : (n ^ 2 - 1) % 3 = 0 := by
    have h3' : (n % 3) = 1 ∨ (n % 3) = 2 := by 
      omega
    rcases h3' with (h3' | h3')
    · -- case n % 3 = 1
      have h30 : (n ^ 2) % 3 = 1 := by 
        have h31 : (n % 3) = 1 := h3'
        norm_num [Nat.pow_mod, h31] at *
      have h4 : (n ^ 2 - 1) % 3 = 0 := by
        omega
      omega
    · -- case n % 3 = 2
      have h30 : (n ^ 2) % 3 = 1 := by 
        have h31 : (n % 3) = 2 := h3'
        norm_num [Nat.pow_mod, h31] at *
      have h4 : (n ^ 2 - 1) % 3 = 0 := by
        omega
      omega
  have h24 : 24 ∣ (n ^ 2 - 1) := by
    omega
  exact h24