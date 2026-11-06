import Mathlib

open Finset

theorem number_theory_1684 {P : ℕ} {r : Finset ℕ} (hr : r = Icc 1 100 \ {50}) (hP : P = ∏ i ∈ r, Nat.factorial i) :
  IsSquare P := by 
  rw [hP, hr]
  native_decide