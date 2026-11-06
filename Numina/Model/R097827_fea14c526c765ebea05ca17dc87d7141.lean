import Mathlib

theorem number_theory_140829 (p : ℕ) (hp : Nat.Prime p) (h : p ≡ 7 [MOD 8]) :
    ¬∃ a b c, a^2 + b^2 + c^2 = p := by
  rintro ⟨a, b, c, h_eq⟩
  have h1 : p % 8 = 7 := h
  have h2 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
    have h : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
      omega
    rcases h with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.add_mod]
    <;> omega
  have h3 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
    have h : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
      omega
    rcases h with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.add_mod]
    <;> omega
  have h4 : c^2 % 8 = 0 ∨ c^2 % 8 = 1 ∨ c^2 % 8 = 4 := by
    have h : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
      omega
    rcases h with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.add_mod]
    <;> omega
  have h5 : (a^2 + b^2 + c^2) % 8 = 7 := by 
    omega -- because h_eq and h1.
  omega -- now using h2, h3, h4 to show that any combination of residues can't be 7.