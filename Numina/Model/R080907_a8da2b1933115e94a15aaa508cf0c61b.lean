import Mathlib

theorem number_theory_7208
    (p : ℕ)
    (h : p.Prime)
    (hpk : p % 4 = 3) :
    ¬∃ a b, p = a ^ 2 + b ^ 2 := by 
  rintro ⟨a, b, h_eq⟩
  have h1 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
    have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2)
    · 
      simp [Nat.pow_mod, h2]
    · 
      simp [Nat.pow_mod, h2]
    · 
      simp [Nat.pow_mod, h2]
    · 
      simp [Nat.pow_mod, h2]
  have h2 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
    have h3 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3)
    · 
      simp [Nat.pow_mod, h3]
    · 
      simp [Nat.pow_mod, h3]
    · 
      simp [Nat.pow_mod, h3]
    · 
      simp [Nat.pow_mod, h3]
  have h3 : (a ^ 2 + b ^ 2) % 4 = 0 ∨ (a ^ 2 + b ^ 2) % 4 = 1 ∨ (a ^ 2 + b ^ 2) % 4 = 2 := by
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> 
      omega 
  have h4 : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 := by 
    have h5 : p = a ^ 2 + b ^ 2 := h_eq
    rw [h5] 
    exact h3 
  omega 
  all_goals linarith
  all_goals linarith
  all_goals linarith