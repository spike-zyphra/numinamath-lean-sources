import Mathlib

theorem algebra_2737 (n : ℕ) (h₁ : n > 40) (h₂ : n < 60) (h₃ : (n * 24) = ∑ i in Finset.Icc 1 n, i) :
    n = 47 := by
  interval_cases n <;> norm_num [Finset.sum_Icc_succ_top] at h₃ <;> omega