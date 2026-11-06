import Mathlib

theorem algebra_196461 (a : ℕ → ℝ) (ha : a 0 = 60 ∧ a 1 = 80)
    (h : ∀ n, a (n + 1) = (∑ i in Finset.range (n + 1), a i) / (n + 1)) :
    a 41 = 70 ∧ a 49 = 70 := by
  have h1 := h 0
  norm_num [Finset.sum_range_succ] at h1
  have h2 : a 0 = 60 := ha.1
  have h3 : a 1 = 80 := ha.2
  linarith