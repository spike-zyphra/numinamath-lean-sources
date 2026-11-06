import Mathlib

theorem algebra_305027 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ n, ∑ i in Finset.Icc 1 n, (1 / a i) = 1 / (∏ i in Finset.Icc 1 n, a i)) :
    (∀ n, 2 ≤ n → a n = a (n + 1)) ∧
    (∀ a1 : ℝ, 0 < a1 ∧ a1 < 1 → ∀ n, 0 < a n ∧ a n < 1) ∧
    (∀ a1 : ℝ, a1 ∉ Set.Icc 0 1 → ∀ n ≥ 2, a n < a (n + 1)) := by

  have h0 := h 0
  norm_num [Finset.sum_eq_zero, Finset.prod_eq_one] at h0
  all_goals nlinarith [ha 0]