import Mathlib

theorem algebra_222998 (a : ℕ → ℕ) (ha : a 1 = 40) (ha' : a 2 = 60)
    (h : ∀ n, a (n + 1) = (∑ i in Finset.Icc 1 n, a i) / n) :
    a 10 = 50 := by
  have h1 := h 0
  norm_num [Finset.sum_eq_zero] at h1
  all_goals omega