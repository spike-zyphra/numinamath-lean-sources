import Mathlib

theorem algebra_250059 {a b : ℝ} {x : ℕ → ℝ} (hx1 : x 1 = a) (hx2 : x 2 = b)
    (hxn : ∀ n ≥ 2, x (n + 1) = x n - x (n - 1)) :
    x 100 = -a ∧ ∑ i in Finset.Icc 1 100, x i = 2 * b - a := by
  constructor
  · -- First prove x 100 = -a
    norm_num [hx1, hx2, hxn]
    <;> ring_nf <;> norm_num
  · -- Then prove ∑ i in Finset.Icc 1 100, x i = 2 * b - a
    norm_num [Finset.sum_Icc_succ_top, hx1, hx2, hxn]
    <;> ring_nf <;> norm_num
    <;> ring