import Mathlib

open Nat

theorem count_div_by_three_100_digit :
  ∃ A : ℕ, A = (4^50 + 2) / 3 := by 
  refine' ⟨(4^50 + 2) / 3, rfl⟩