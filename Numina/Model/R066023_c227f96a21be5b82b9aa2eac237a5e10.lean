import Mathlib

theorem algebra_285999 (m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
    (h1 : ∀ x y, m * x + n * y ^ 2 = 0 → m * x ^ 2 + n * y ^ 2 = 1) :
    ∃ x y, m * x + n * y ^ 2 = 0 := by
  exact ⟨0, 0, by ring⟩