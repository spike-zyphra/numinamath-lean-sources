import Mathlib

open Finset

theorem number_theory_82595 {n : ℕ} (hn : n ≠ 0) :
    Even n → {k | k < n ∧ Even (Nat.primeFactors (Nat.gcd n k)).card}.encard =
    {k | k < n ∧ Odd (Nat.primeFactors (Nat.gcd n k)).card}.encard ∧
    Odd n → {k | k < n ∧ Even (Nat.primeFactors (Nat.gcd n k)).card}.encard >
    {k | k < n ∧ Odd (Nat.primeFactors (Nat.gcd n k)).card}.encard := by
  intro h1 h2
  exfalso
  have h3 : Odd n := h2.right
  have h4 : ¬ Odd n := by
    have h' : Even n := h1
    have : ¬ Odd n := by
      obtain ⟨m, hm⟩ := h'
      simp [Nat.odd_iff, hm]
      <;> omega
    assumption
  contradiction