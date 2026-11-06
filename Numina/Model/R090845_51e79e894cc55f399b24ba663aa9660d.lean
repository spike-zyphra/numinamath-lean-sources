import Mathlib

theorem algebra_10725 {a : ℕ → ℝ} (ha1 : a 1 = 5)
    (han : ∀ n ≥ 2, a n = (2 * a (n - 1) - 1) / (a (n - 1) - 2)) :
    ∑ i in Finset.Icc 1 100, a i = 400 := by
  norm_num [Finset.sum_Icc_succ_top, ha1, han]
  <;> norm_num
  <;> ring_nf <;> norm_num