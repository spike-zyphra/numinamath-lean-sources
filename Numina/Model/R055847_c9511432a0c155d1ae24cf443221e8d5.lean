import Mathlib

theorem number_theory_137498 :
    ∃ n : ℕ, 2019 ∣ n ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 2019] := by
  use 0
  constructor
  · exact dvd_zero 2019
  · simp [Nat.ModEq, Nat.digits, Nat.digitsAux]