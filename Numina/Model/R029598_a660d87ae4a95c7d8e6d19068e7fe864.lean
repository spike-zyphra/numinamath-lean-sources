import Mathlib

theorem number_theory_112631 :
    ¬∃ a b : ℕ, 11 ∣ a^2 + b^2 ∧ ¬(11 ∣ a) ∧ ¬(11 ∣ b) := by
  rintro ⟨a, b, h1, h2, h3⟩
  have h4 : a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by
    omega
  have h5 : b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by
    omega
  have h6 : (a ^ 2 + b ^ 2) % 11 = 0 := by
    omega
  rcases h4 with (h | h | h | h | h | h | h | h | h | h) <;> rcases h5 with (h' | h' | h' | h' | h' | h' | h' | h' | h' | h') <;> simp [Nat.add_mod, Nat.mul_mod, pow_two, h, h'] at h6 <;> omega