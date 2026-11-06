import Mathlib

open Finset Real

theorem algebra_102885 : ∃ a b : ℕ, a.gcd b = 1 ∧ ∑ i ∈ range 100, (1 / ((i + 1) * (i + 2) * (i + 3))) = a / b := by 
  use 99, 404
  native_decide