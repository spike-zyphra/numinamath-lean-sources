import Mathlib

theorem algebra_110206 {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (h : ∀ n, ∑ i ∈ Finset.range (n + 1), (a + (i * d)) = 2 ^ n * a + (2 ^ n - 2) * d)
    (h' : ∃ n, ∑ i ∈ Finset.range (n + 1), (a + (i * d)) = 1988) :
    n = 6 ∧ a = 2 ∧ d = 30 := by

  have h1 := h 1

  simp [Finset.sum_range_succ] at h1

  all_goals
    omega