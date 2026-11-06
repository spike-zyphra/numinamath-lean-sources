import Mathlib

theorem algebra_20134 {f : ℝ → ℝ} (hf : ∀ x, f x = x - ⌊√x⌋ ^ 2) :
    ∑ i ∈ Finset.Icc 101 (110 : ℕ), f i = 55 := by
  norm_num [Finset.sum_Icc_succ_top, hf]