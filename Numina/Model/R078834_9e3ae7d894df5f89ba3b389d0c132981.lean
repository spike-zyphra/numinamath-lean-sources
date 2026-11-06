import Mathlib

theorem number_theory_249166
    (a b c : ℕ)
    (h₀ : Odd a)
    (h₁ : Odd b)
    (h₂ : Odd c) :
    4 ∣ (a * b - 1) ∨ 4 ∣ (b * c - 1) ∨ 4 ∣ (a * c - 1) := by
  have h3 : a % 4 = 1 ∨ a % 4 = 3 := by 
    rcases h₀ with ⟨k, hk⟩
    have : a % 4 = 1 ∨ a % 4 = 3 := by 
      omega
    exact this
  have h4 : b % 4 = 1 ∨ b % 4 = 3 := by 
    rcases h₁ with ⟨k, hk⟩
    have : b % 4 = 1 ∨ b % 4 = 3 := by 
      omega
    exact this
  have h5 : c % 4 = 1 ∨ c % 4 = 3 := by 
    rcases h₂ with ⟨k, hk⟩
    have : c % 4 = 1 ∨ c % 4 = 3 := by 
      omega
    exact this
  rcases h3 with (h3 | h3)
  · rcases h4 with (h4 | h4)
    · rcases h5 with (h5 | h5)
      · -- a % 4 = 1, b % 4 = 1, c % 4 = 1
        have h6 : (a * b) % 4 = 1 := by 
          simp [Nat.mul_mod, h3, h4]
        have h7 : 4 ∣ (a * b - 1) := by 
          omega
        left
        exact h7
      · -- a % 4 = 1, b % 4 = 1, c % 4 = 3
        have h6 : (a * b) % 4 = 1 := by 
          simp [Nat.mul_mod, h3, h4]
        have h7 : 4 ∣ (a * b - 1) := by 
          omega
        left
        exact h7
    · rcases h5 with (h5 | h5)
      · -- a % 4 = 1, b % 4 = 3, c % 4 = 1
        have h11 : 4 ∣ (a * c - 1) := by
          have h12 : (a * c) % 4 = 1 := by 
            simp [Nat.mul_mod, h3, h5]
          omega
        right
        right
        exact h11
      · -- a % 4 = 1, b % 4 = 3, c % 4 = 3
        have h9 : 4 ∣ (b * c - 1) := by
          have h6 : (b * c) % 4 = 1 := by 
            simp [Nat.mul_mod, h4, h5]
          omega
        right
        left
        exact h9
  · rcases h4 with (h4 | h4)
    · rcases h5 with (h5 | h5)
      · -- a % 4 = 3, b % 4 = 1, c % 4 = 1
        have h9 : 4 ∣ (b * c - 1) := by
          have h6 : (b * c) % 4 = 1 := by 
            simp [Nat.mul_mod, h4, h5]
          omega
        right
        left
        exact h9
      · -- a % 4 = 3, b % 4 = 1, c % 4 = 3
        have h9 : 4 ∣ (a * c - 1) := by
          have h6 : (a * c) % 4 = 1 := by 
            simp [Nat.mul_mod, h3, h5]
          omega
        right
        right
        exact h9
    · rcases h5 with (h5 | h5)
      · -- a % 4 = 3, b % 4 = 3, c % 4 = 1
        have h6 : (a * b) % 4 = 1 := by 
          simp [Nat.mul_mod, h3, h4]
        have h7 : 4 ∣ (a * b - 1) := by 
          omega
        left
        exact h7
      · -- a % 4 = 3, b % 4 = 3, c % 4 = 3
        have h9 : 4 ∣ (b * c - 1) := by
          have h6 : (b * c) % 4 = 1 := by 
            simp [Nat.mul_mod, h4, h5]
          omega
        right
        left
        exact h9