import Mathlib

open Real
open scoped BigOperators

theorem algebra_3788 {f : ℝ → ℝ} (hf : ∀ x, f x = (x^2 - 2 * x + 3) / (x - 1)) :
    ∑ i : ℕ in Finset.Icc 2 10, ⌊f i⌋ = 48 := by
  norm_num [Finset.sum_Icc_succ_top, hf, Int.floor_eq_iff]
  <;> norm_num