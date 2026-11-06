import Mathlib

theorem algebra_298397 {a : ℕ → ℝ} (h : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (h' : ∀ n, ∑ i in Finset.range n, a i = ((a n + 1) ^ 2) / 4) :
    ∑ i in Finset.range 20, a i = 0 := by
  have eq0 := h' 0
  norm_num [Finset.sum_empty] at eq0
  have ha0 : a 0 = -1 := by
    nlinarith
  rcases h with ⟨r, hr⟩
  have eq1 := h' 1
  simp [Finset.sum_range_succ, ha0] at eq1
  have ha1 : a 1 = a 0 * r ^ 1 := hr 1
  rw [ha1, ha0] at eq1
  all_goals
    nlinarith [sq_nonneg (a 0 * r ^ 1 + 1), sq_nonneg (r - 1)]