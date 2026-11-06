import Mathlib

theorem number_theory_110871 (p n : ℕ) (hp : Nat.Prime p) : p ∣ n ∨ Nat.Coprime p n := by 
  have h := Nat.coprime_or_dvd_of_prime hp n
  cases h with
  | inl h =>
      right
      exact h
  | inr h =>
      left
      exact h