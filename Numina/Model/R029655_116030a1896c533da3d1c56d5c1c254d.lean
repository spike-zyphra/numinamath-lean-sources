import Mathlib

theorem number_theory_195033 (p : ℕ) (hp : p.Prime) (h : p ≡ 7 [MOD 8]) :
    ¬∃ a b c, p = a^2 + b^2 + c^2 := by
  rintro ⟨a, b, c, heq⟩
  have h1 : p % 8 = 7 := h
  have h2 : (a^2 + b^2 + c^2) % 8 = 0 ∨ (a^2 + b^2 + c^2) % 8 = 1 ∨ (a^2 + b^2 + c^2) % 8 = 2 ∨ (a^2 + b^2 + c^2) % 8 = 3 ∨ (a^2 + b^2 + c^2) % 8 = 4 ∨ (a^2 + b^2 + c^2) % 8 = 5 ∨ (a^2 + b^2 + c^2) % 8 = 6 := by
    have h1' : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
      omega
    have h2' : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
      omega
    have h3' : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
      omega
    rcases h1' with (h1' | h1' | h1' | h1' | h1' | h1' | h1' | h1') <;> rcases h2' with (h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2') <;> rcases h3' with (h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3') <;> simp [Nat.add_mod, Nat.mul_mod, pow_two, h1', h2', h3']
  have h3 : p % 8 = (a^2 + b^2 + c^2) % 8 := by
    omega
  omega