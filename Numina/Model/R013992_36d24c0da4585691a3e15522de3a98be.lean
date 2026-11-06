import Mathlib
open scoped BigOperators

theorem algebra_9136 {k : ℕ} (hk : 0 < k) (a : ℕ → ℝ)
  (ha0 : a 0 = 1 / k) (han : ∀ n, a (n + 1) = a n + (1 / (n + 1)^2) * (a n)^2)
  (h : ∀ n, 0 < n → a n < 1) :
  k ≥ 3 := by
  by_contra h1
  push_neg at h1
  have hk1 : k = 1 ∨ k = 2 := by
    have h2 : k < 3 := by linarith
    interval_cases k <;> tauto
  rcases hk1 with (rfl | rfl)
  · -- k = 1
    have h10 : a 1 ≥ 1 := by
      norm_num [ha0, han]
      all_goals
      nlinarith
    have h11 : a 1 < 1 := h 1 (by norm_num)
    linarith
  · -- k = 2
    have h10 : a 4 ≥ 1 := by
      norm_num [ha0, han]
      all_goals
      nlinarith
    have h11 : a 4 < 1 := h 4 (by norm_num)
    linarith