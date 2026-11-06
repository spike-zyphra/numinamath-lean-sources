import Mathlib

theorem number_theory_161655 : ¬∃ n m, 19^19 = n^3 + m^4 := by 
  rintro ⟨n, m, h_eq⟩
  have h1 : n^3 + m^4 = 19^19 := by linarith
  have h4 : (n^3 + m^4) % 13 = 7 := by
    omega
  have h2 : n^3 % 13 = 0 ∨ n^3 % 13 = 1 ∨ n^3 % 13 = 3 ∨ n^3 % 13 = 5 ∨ n^3 % 13 = 8 ∨ n^3 % 13 = 12 := by 
    have h : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by 
      omega
    rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod] at *
  have h3 : m^4 % 13 = 0 ∨ m^4 % 13 = 1 ∨ m^4 % 13 = 3 ∨ m^4 % 13 = 9 := by 
    have h : m % 13 = 0 ∨ m % 13 = 1 ∨ m % 13 = 2 ∨ m % 13 = 3 ∨ m % 13 = 4 ∨ m % 13 = 5 ∨ m % 13 = 6 ∨ m % 13 = 7 ∨ m % 13 = 8 ∨ m % 13 = 9 ∨ m % 13 = 10 ∨ m % 13 = 11 ∨ m % 13 = 12 := by 
      omega
    rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod] at *
  omega