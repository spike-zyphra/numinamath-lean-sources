import Mathlib


open Nat


theorem number_theory_92655 (a b c : ℕ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : ∃ m, m^2 = a * b + 1) (h₃ : ∃ n, n^2 = b * c + 1) (h₄ : ∃ p, p^2 = c * a + 1) :
    4 ∣ a ∨ 4 ∣ b ∨ 4 ∣ c := by
  by_contra h
  push_neg at h
  rcases h₂ with ⟨m, hm⟩
  rcases h₃ with ⟨n, hn⟩
  rcases h₄ with ⟨p, hp⟩
  have h8 : m^2 % 8 = 0 ∨ m^2 % 8 = 1 ∨ m^2 % 8 = 4 := by
    have h1 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
  have h8' : n^2 % 8 = 0 ∨ n^2 % 8 = 1 ∨ n^2 % 8 = 4 := by
    have h1 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
  have h8'' : p^2 % 8 = 0 ∨ p^2 % 8 = 1 ∨ p^2 % 8 = 4 := by
    have h1 : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨ p % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
  have h9 : (a * b + 1) % 8 = m^2 % 8 := by omega
  have h10 : (b * c + 1) % 8 = n^2 % 8 := by omega
  have h11 : (c * a + 1) % 8 = p^2 % 8 := by omega
  have ha2 : a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
    omega
  have hb2 : b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
    omega
  have hc2 : c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    omega
  -- Now analyze all possible products
  rcases ha2 with (h12 | h12 | h12 | h12 | h12 | h12) <;> rcases hb2 with (h13 | h13 | h13 | h13 | h13 | h13) <;> rcases hc2 with (h14 | h14 | h14 | h14 | h14 | h14) <;> 
    simp [Nat.add_mod, Nat.mul_mod, h12, h13, h14] at h9 h10 h11 <;> omega