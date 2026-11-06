import Mathlib

open Nat Finset

theorem number_theory_45633 {g : Finset ℕ} (hg : g = Ico 1 101 \ {50}) :
    IsSquare (∏ i ∈ g, i !) := by
  rw [hg]
  native_decide