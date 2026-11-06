import Mathlib

theorem number_theory_168475 (a : ℕ → ℕ) (ha : ∀ k, 0 < a (2 * k - 1) ∧ 0 < a (2 * k))
    (h1 : ∀ k, a (2 * k - 1) + a (2 * k) = 2 ^ k) (h2 : ∀ m, ∃ l, 0 < l ∧ l ≤ m ∧ a (m + 1) = ∑ i in Finset.Icc l m, a i) :
    IsGreatest {∑ i in Finset.range 1011, a (2 * i + 2)} ((2 ^ 1013 - 5) / 3) := by
  have h3 := h2 0
  norm_num at h3
  all_goals
    omega