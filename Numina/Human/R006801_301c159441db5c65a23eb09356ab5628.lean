import Mathlib

open Nat

theorem number_theory_641275 (k : ℕ) (hk : 0 < k) :
  ∀ n : ℕ, ∃ p : Fin k → ℕ, (∀ i j, p i = p j → i = j) ∧ (∀ i, p i > n) ∧
  (∀ i, Nat.Prime (p i)) := by 
  intro n
  let p : Fin k → ℕ := fun i => Nat.nth Nat.Prime (i + n)
  use p
  constructor
  · intro i j hij
    unfold p at hij
    obtain h1 := Nat.nth_injective infinite_setOf_prime
    unfold Function.Injective at h1
    have aux1 : i + n = j + n := by 
      exact h1 hij
    omega
  constructor
  · intro i
    unfold p
    obtain h1 := add_two_le_nth_prime (i + n)
    linarith
  · intro i
    unfold p
    exact prime_nth_prime (↑i + n)
