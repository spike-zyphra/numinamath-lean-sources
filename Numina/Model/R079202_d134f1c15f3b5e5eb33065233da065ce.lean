import Mathlib

open Finset

theorem number_theory_189872 {n : ℕ} (hn : n = 1985) :
    Odd n ↔ (Nat.digits 2 n).headI ≠ 0 ∧ (Nat.digits 3 n).headI ≠ 0 := by
  rw [hn]
  native_decide