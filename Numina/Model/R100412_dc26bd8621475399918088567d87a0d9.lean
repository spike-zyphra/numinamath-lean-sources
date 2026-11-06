import Mathlib

theorem algebra_283618 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
    (h1 : ∀ x y, m * x + n * y ^ 2 = 0 → m * x ^ 2 + n * y ^ 2 = 1) :
    m = -1 ∧ n = 1 := by 
  have h2 := h1 0 0 (by ring)
  simp at h2 
  all_goals 
    contradiction