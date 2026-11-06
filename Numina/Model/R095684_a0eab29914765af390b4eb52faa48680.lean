import Mathlib

theorem number_theory_284304 (a : ℕ → ℕ → ℕ)
    (h₀ : ∀ n m, a n m = a (n - 1) (m - 1) + 1)
    (h₁ : a 0 0 = 9) :
    ∃ r c, a r c = 1997 := by
  have h2 := h₀ 0 0
  simp at h2
  all_goals
    omega