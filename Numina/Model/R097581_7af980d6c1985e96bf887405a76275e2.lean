import Mathlib

theorem number_theory_239682 (n : ℕ) (hn : Odd n) :
    ∃ m, n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, Odd d := by 
  use 0 
  constructor 
  · -- Show that n divides 0
    simp 
  · -- Show that all digits of 0 are odd
    intro d 
    intro hd 
    simpa using hd