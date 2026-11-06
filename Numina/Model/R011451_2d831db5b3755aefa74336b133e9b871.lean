import Mathlib

open Nat Finset

def solset : Finset (ℕ × ℕ) := ((Finset.range 1000).product (Finset.range 1000)).filter fun ⟨x, y⟩ => 0 < x ∧ 0 < y ∧ 50 * x + 60 * y = 1220

theorem algebra_624533 : solset.card = 4 := by
  native_decide