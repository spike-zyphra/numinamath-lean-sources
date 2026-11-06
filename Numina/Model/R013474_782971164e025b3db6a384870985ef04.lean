import Mathlib

theorem number_theory_158721 (n : ℕ) (h₀ : n = ∑ i ∈ Finset.range 300, 10 ^ i) :
    ¬ ∃ m, m^2 = n := by
  intro h
  rcases h with ⟨m, hm⟩
  rw [h₀] at hm
  have h1 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have h2 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, Nat.mul_mod, h2]
  have h2 : ( ∑ i in Finset.range 300, 10 ^ i ) % 4 = 3 := by
    native_decide
  have h3 : m ^ 2 % 4 = 3 := by 
    omega
  omega