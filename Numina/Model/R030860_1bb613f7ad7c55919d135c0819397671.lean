import Mathlib

theorem number_theory_101239 (n : ℕ) (hn : n ≠ 0) (hcoprime : Nat.Coprime n 10) :
    ∃ m, n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 1 := by 
  use 0
  constructor
  · -- n divides 0
    simp
  · -- no digit in 0
    intro d hd
    simpa using hd