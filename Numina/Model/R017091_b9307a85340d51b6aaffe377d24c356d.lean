import Mathlib

theorem number_theory_137299 (a b c : ℕ) :
    7 ∣ a^2 + b^2 + c^2 → 7 ∣ a^4 + b^4 + c^4 := by
  intro h
  -- Let's think about how to solve this problem using modular arithmetic in Lean 4
  have h1 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by 
    omega
  have h2 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by 
    omega
  have h3 : c % 7 = 0 ∨ c % 7 = 1 ∨ c % 7 = 2 ∨ c % 7 = 3 ∨ c % 7 = 4 ∨ c % 7 = 5 ∨ c % 7 = 6 := by 
    omega
  
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h1, h2, h3] at h ⊢
   <;> omega