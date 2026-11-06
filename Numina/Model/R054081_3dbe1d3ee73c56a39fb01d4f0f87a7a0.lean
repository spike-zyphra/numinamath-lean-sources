import Mathlib

theorem algebra_205281 {f : ℤ → ℤ} (hf : ∀ n, f n = 4 * n ^ 3 - 6 * n ^ 2 + 4 * n + 13) :
    ∑ i in Finset.Icc 1 13, f i = 28743 := by
  norm_num [Finset.sum_Icc_succ_top, hf]
  <;> rfl