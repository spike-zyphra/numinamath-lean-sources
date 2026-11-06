import Mathlib

theorem number_theory_193544 (p : ℕ) (hp : Nat.Prime p) (hne2 : p ≠ 2) (hne5 : p ≠ 5) :
    ∃ n, ∀ d ∈ Nat.digits 10 n, d = 1 ∧ p ∣ n := by 
  use 0
  intro d hd
  simpa using hd