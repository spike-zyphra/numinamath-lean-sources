import Mathlib

theorem number_theory_167941 (a : ℕ) (h₀ : ¬ 5 ∣ a) :
    100 ∣ a^8 + 3 * a^4 - 4 := by

  have h2 : (a ^ 8 + 3 * a ^ 4) % 4 = 0 := by
    have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
      omega
    rcases h1 with (h | h | h | h)
    · 
      simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]

  have h4 : (a ^ 8 + 3 * a ^ 4) % 25 = 4 := by
    have h5 : a % 25 = 1 ∨ a % 25 = 2 ∨ a % 25 = 3 ∨ a % 25 = 4 ∨
      a % 25 = 6 ∨ a % 25 = 7 ∨ a % 25 = 8 ∨ a % 25 = 9 ∨
      a % 25 = 11 ∨ a % 25 = 12 ∨ a % 25 = 13 ∨ a % 25 = 14 ∨
      a % 25 = 16 ∨ a % 25 = 17 ∨ a % 25 = 18 ∨ a % 25 = 19 ∨
      a % 25 = 21 ∨ a % 25 = 22 ∨ a % 25 = 23 ∨ a % 25 = 24 := by
      omega
    rcases h5 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]

  omega