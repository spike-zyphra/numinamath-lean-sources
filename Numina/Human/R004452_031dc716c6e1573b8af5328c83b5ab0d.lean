import Mathlib

theorem number_theory_269047 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : n < 100)
    (h₂ : Nat.ofDigits 10 (List.reverse (Nat.digits 10 (2 * n))) + 2 = 27) :
    n = 26 := by 
  by_contra! h
  interval_cases n
  <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at *