import Mathlib

theorem algebra_103430 (M : ℕ → ℝ) (hM : ∀ n, M n = ∑ i in Finset.range n, 2 ^ i) :
    M 200 - M 1 = 2 ^ 200 - 2 := by 
  rw [hM 200, hM 1]
  norm_num [Finset.sum_range_succ]