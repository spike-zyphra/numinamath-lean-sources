import Mathlib

open Finset Real Int Nat

theorem algebra_16904 : ∏ i ∈ range 5, ⌊(-i - 0.5 : ℝ)⌋ * ⌈(i + 0.5 : ℝ)⌉ = -14400 := by
  norm_num [prod_range_succ, Int.floor_eq_iff, Int.ceil_eq_iff]