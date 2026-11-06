import Mathlib

theorem number_theory_160780 (p : ℕ) (hp : Nat.Prime p) :
    Irrational (Real.sqrt p) := by
  apply Nat.Prime.irrational_sqrt
  exact hp