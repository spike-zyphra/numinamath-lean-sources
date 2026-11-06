import Mathlib

theorem number_theory_248905 (a : ℕ) (ha : a = 2017^2017) (n : ℕ) (hn : n = 26)
    (h : ∃ d : ℕ, d < n ∧ a - 2 * d = ∑ i ∈ Finset.range n, (2 * i - 2 * d)) :
    False := by
  rcases h with ⟨d, hd1, h_eq⟩
  rw [ha, hn] at h_eq
  norm_num [Finset.sum_range_succ] at h_eq
  all_goals
    omega